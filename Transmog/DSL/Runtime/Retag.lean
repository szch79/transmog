/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Compiler.LCNF.ToImpureType

/-!
# Overriding the IR classification of a word-backed type

The compiler classifies every inductive once, in its declaring module, into one of the IR types
that decide how the backend treats a value of it.  A type whose every constructor carries a field
is classified as a definite heap reference, and the reference counting pass then emits the
untested increment and decrement on it.  A word-backed value is never a heap reference, so once
its runtime representation has been replaced that classification is wrong, and an untested
decrement dereferences the boxed word.

This module rewrites the classification to `tagged`, the IR type of a value that is always a boxed
scalar, which is precisely what a word-backed value is.  A `tagged` value receives no reference
counting at all, so the rewrite also removes the tested no-op operations that a possibly-tagged
classification would still emit.

The classification table is private to the compiler.  It is recovered by name from the registry of
persistent environment extensions, and every write is read back through the compiler's public
accessor, so that a change to the table in a future toolchain fails at the clause rather than in
generated code.
-/

public meta section

namespace Transmog.Runtime

open Lean Compiler LCNF

/-- The user-facing name of the compiler's classification table. -/
def impureTypeExtName : Name := `Lean.Compiler.LCNF.impureTypeExt

/--
The compiler's classification table, recovered by name from the registered persistent extensions.
The registry erases the extension's entry and state types, so the recovered extension is a
reinterpretation that carries no guarantee beyond its name.
-/
private unsafe def findImpureTypeExtUnsafe : IO (MapDeclarationExtension Expr) := do
  let exts ← persistentEnvExtensionsRef.get
  let found := exts.filter fun ext => privateToUserName ext.name == impureTypeExtName
  match found with
  | #[ext] => return ⟨unsafeCast ext⟩
  | #[] => throw <| .userError s!"no persistent environment extension is named \
      `{impureTypeExtName}`; the compiler's classification table cannot be overridden"
  | _ => throw <| .userError s!"several persistent environment extensions are named \
      `{impureTypeExtName}`; the compiler's classification table cannot be identified"

@[implemented_by findImpureTypeExtUnsafe]
opaque findImpureTypeExt : IO (MapDeclarationExtension Expr)

/--
Reclassify the inductive `typeName`, which must be declared in the module being elaborated, as
`tagged`, and confirm the new classification through the compiler's own accessor.  The
classification is consulted whenever code touching the type is lowered to the impure phase, so
the call has to come before any such code is compiled, including the helpers of the type's own
runtime representation.
-/
def retagAsTagged (typeName : Name) : CoreM Unit := do
  if let some modIdx := (← getEnv).getModuleIdxFor? typeName then
    throwError m!"`{.ofConstName typeName}` is declared in \
      `{(← getEnv).allImportedModuleNames[modIdx]!}`, so its IR classification cannot be \
      overridden here"
  let ext ← findImpureTypeExt
  modifyEnv (ext.insert · typeName ImpureType.tagged)
  let after ← nameToImpureType typeName
  unless after == ImpureType.tagged do
    throwError m!"internal error: the IR classification of `{.ofConstName typeName}` reads back \
      as `{after}` after it was overridden to `{ImpureType.tagged}`; the compiler's \
      classification table has changed and `replace_runtime` cannot reclassify types on this \
      toolchain"

end Transmog.Runtime

end -- public meta section
