/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Environment
public meta import Lean.CoreM

/-!
# Registry of word-backed runtime representations

A registered inductive keeps its logical form but is represented at runtime by a boxed unsigned
integer of the recorded carrier width.  The registry records the generated helpers that mediate
between the two views, so that the code generator can route every construction and every
elimination through them.

The entry is written by the `replace_runtime` clause in the module that declares the type, and read
by the compiler passes in every module that compiles code touching it.  Nothing here interprets the
helpers; their meaning is fixed by the clause that generated them.
-/

public meta section

namespace Transmog.Runtime

open Lean

/--
The generated helpers of one word-backed type.  Constructor-indexed arrays follow the declaration
order of the inductive, so index `i` always refers to the constructor with constructor index `i`.
-/
structure ReprInfo where
  /-- The unsigned integer type holding the packed value, one of `UInt8`, `UInt16` and `UInt32`. -/
  carrier : Name
  /-- The constructors, in constructor-index order. -/
  ctors : Array Name
  /-- Reinterprets a value of the type as its packed word. -/
  word : Name
  /-- Builds a value of the type from the constructor's fields, one per constructor. -/
  ctorImpls : Array Name
  /-- Decides a constructor's guard on the packed word; `none` for the unguarded constructor. -/
  tests : Array (Option Name)
  /-- Extracts a constructor field from the packed word, per constructor and then per field. -/
  fields : Array (Array Name)
  /-- The guarded constructor indices in guard-test order, which is first-match order. -/
  order : Array Nat
  /-- The constructor index of the unguarded constructor, if the declaration has one. -/
  unguarded? : Option Nat
  /--
  Declarations that were compiled against the native layout and must therefore never be called.
  Reaching one means some elimination escaped the rewrite.
  -/
  forbidden : Array Name
deriving Inhabited

/-- The registry, indexed for the three lookups the compiler passes perform. -/
structure Registry where
  /-- Word-backed types, by type name. -/
  types : NameMap ReprInfo := {}
  /-- Constructors of word-backed types, mapped to their type and constructor index. -/
  ctors : NameMap (Name × Nat) := {}
  /-- Forbidden declarations, mapped to the type that forbids them. -/
  forbidden : NameMap Name := {}
deriving Inhabited

/-- Whether any type is registered.  The compiler passes return immediately when none is. -/
def Registry.isEmpty (s : Registry) : Bool :=
  s.types.isEmpty

/-- Record `info` for `typeName`, filling in the derived indices. -/
def Registry.insert (s : Registry) (typeName : Name) (info : ReprInfo) : Registry := Id.run do
  let mut ctors := s.ctors
  for h : i in [0:info.ctors.size] do
    ctors := ctors.insert info.ctors[i] (typeName, i)
  let mut forbidden := s.forbidden
  for name in info.forbidden do
    forbidden := forbidden.insert name typeName
  return { types := s.types.insert typeName info, ctors, forbidden }

/--
The registry is persisted so that the compiler passes see every type reachable from the module
being compiled, not only the ones declared in it.
-/
initialize reprExt : SimplePersistentEnvExtension (Name × ReprInfo) Registry ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (typeName, info) => s.insert typeName info
    addImportedFn := fun ess =>
      ess.foldl (init := {}) fun s es =>
        es.foldl (init := s) fun s (typeName, info) => s.insert typeName info
    asyncMode := .sync
  }

/-- The registry as seen from `env`. -/
def getRegistry (env : Environment) : Registry :=
  reprExt.getState env

/-- The recorded helpers of `typeName`, if it is word-backed. -/
def reprInfo? (env : Environment) (typeName : Name) : Option ReprInfo :=
  (getRegistry env).types.find? typeName

/-- Register `info` for `typeName`, which must be declared in the module being elaborated. -/
def registerReprInfo (typeName : Name) (info : ReprInfo) : CoreM Unit := do
  if let some modIdx := (← getEnv).getModuleIdxFor? typeName then
    throwError m!"`{.ofConstName typeName}` is declared in \
      `{(← getEnv).allImportedModuleNames[modIdx]!}`, so its runtime representation cannot be \
      registered here; the clause must appear in the module that declares the type"
  modifyEnv (reprExt.addEntry · (typeName, info))

end Transmog.Runtime

end -- public meta section
