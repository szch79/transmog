/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Parser.Syntax
public meta import Transmog.Init

/-! # Transmog DSL syntax -/

public meta section

namespace Transmog

/-- A range denotes a bit slice of an unsigned integer type. -/
declare_syntax_cat transmogReprRange
/-- A single bit slice, using zero-based indexing. -/
syntax (name := transmogReprRange.bit) "[" num "]" : transmogReprRange
/--
A half-open interval of bits `[m:n]`, from bit `m` to bit `n - 1`, using zero-based indexing.
Either one of the bounds can be omitted: `m` defaults to `0`, and `n` defaults to the width of the
data type being modified, and thus `[:]` denotes the full range.
-/
syntax (name := transmogReprRange.range) "[" (num)? ":" (num)? "]" : transmogReprRange

/--
A place in the representation denotes a physical region in which data resides.  It can be either a
value of unsigned integer type or a slice of it.

`ident` should always be a variable of one of the unsigned integer types.
-/
syntax transmogReprPlace := ident (transmogReprRange)?

/--
The type of a slot in the representation array.  It must be an unsigned integer type following
by an optional range of bits (without exceeding the physical bit size of the base type).
-/
syntax transmogReprSlotTy := ident (transmogReprRange)?
/--
A representation slot.  As opposed to logical fields in the actual Lean type, representation slots
are the physical fields storing the data, typed with one of the unsigned integers.

A representation slot is declared with the identifier for referring it, followed by its type and
optional constraints.  The syntax is deliberately made similar to Lean's subtyping, because under
the hood we do use subtyping to help plumbing the data and the representation invariants.

For example, the lower 31 bits of a `UInt32` can be declared as `r : UInt32 // r.fitsBits 31`,
where `UInt32.fitsBits` is an auxiliary definition that clamps the use of `r` in the lower 31 bits.
Note that `r` is just an arbitrarily chosen name for the data.

Representation slots do not have to correspond strictly to logical fields.  For example, one can
represent an enum with one `UInt8` slot (a simple case that Lean's compiler already does).
-/
syntax transmogReprSlot := ident " : " transmogReprSlotTy (" // " term)?
/--
A specification of representation slots is an array of representation slots.  All data from the
actual logical Lean type should be able to be written to/recovered from the slots.

Declaration order of the slots might be used for the layout, depending on the layout algorithm
used.
-/
syntax transmogReprSpec := "[" transmogReprSlot,+ "]"

/--
The value assignment to a field of the actual logical Lean type, from the representation slot
data.
-/
declare_syntax_cat transmogReprFieldValue
/--
The value assignment using a place.  For example, `r[2:11]` denotes the data stored in bit 2 to bit
10 of `r`.
-/
syntax (name := transmogReprFieldValue.place) transmogReprPlace : transmogReprFieldValue
/-- The value assignment with a transformation gadget applied to another valid value asssignment. -/
syntax (name := transmogReprFieldValue.transform)
  withPosition(ident colGt transmogReprFieldValue) : transmogReprFieldValue
/-- The value assignment using a product of valid value assignments. -/
syntax (name := transmogReprFieldValue.prod)
  "(" transmogReprFieldValue,+ ")" : transmogReprFieldValue

/-- The conditional guard discriminating constructors of an inductive type. -/
syntax transmogReprGuard := withPosition(colGe ppLine &"guard " term)

/-- Declares how fields and representation slots are written. -/
declare_syntax_cat transmogReprWrite
/--
Declares how a field in the actual logical Lean type is assigned from the representation value.
This will be used directly for the `fromRepr` direction, and the `toRepr` direction will also be
inferred accordingly.
-/
syntax (name := transmogReprWrite.field)
  ident " : " term:51 " <= " transmogReprFieldValue : transmogReprWrite
/--
Declares a hint on how a representation slot is written in the `toRepr` direction, and the
`fromRepr` direction will be inferred accordingly.

A slot that neither a field value assignment nor an equation in the guard determines is written
as zero, so a hint is needed only where another value is wanted.  For example, the tag slot of the
unguarded constructor of an inductive type usually needs one.  A hint that repeats a write the
guard already determines is accepted, and one that contradicts it is rejected.
-/
syntax transmogReprHint := transmogReprPlace " := " term
syntax (name := transmogReprWrite.hint) transmogReprHint : transmogReprWrite

/--
The keywords that open a clause after the body.  They are not reserved, so a write list has to
stop in front of them explicitly; otherwise a clause following a constructor without writes
would be read as a write.
-/
syntax transmogClauseKeyword := &"replace_runtime" <|> &"derive_layout" <|> &"correct_by"

syntax transmogReprWrites :=
  manyIndent(ppLine notFollowedBy(transmogClauseKeyword) transmogReprWrite)

/--
Declares representation for an inductive constructor.

Example:
```lean
| ctor =>
  guard tag = 1
  a : { x : UInt32 // x.fitsBits 12 } <= r[:12]
  b : { x : UInt32 // x.fitsBits 20 } <= r[12:]
```
declares how the `ctor` constructor is represented.  It has two constructor arguments, `a` and `b`,
both represented by bounded unsigned integers.  Their values come from the representation slot
`r`, where `a` takes the value in bit 0 to bit 11, and `b` takes the rest.  There's another
representation slot, `tag`, which is used to tag the constructor.  The `guard` statement asserts
that in the `fromRepr` direction, this constructor is recognized when `tag = 1`, and in the
`toRepr` direction it determines the write `tag := 1`, which the field values `a` and `b` alone
could not.  A guard is a conjunction of assertions, and every equation between a slot and a value
determines such a write; a slot that neither a guard equation nor a field determines needs an
explicit hint.
-/
syntax transmogReprCtor :=
  ppIndent(ppLine "| " ident " => " (transmogReprGuard)? transmogReprWrites)

/--
The body of a Transmog representation.  It is either one or more constructor representations, if the
logical Lean type is an inductive type, or one or more field representations, if the type is a
structure.
-/
declare_syntax_cat transmogReprBody
syntax (name := transmogReprBody.ctors) (transmogReprCtor)+ : transmogReprBody
syntax (name := transmogReprBody.writes) transmogReprWrites : transmogReprBody

/-- Layout ordering. -/
declare_syntax_cat transmogLayoutOrder (behavior := symbol)
/-- Use the natural ordering of representation slots in the layout. -/
syntax (name := transmogLayoutOrder.c) &"C" : transmogLayoutOrder
/-- Reorder representation slots in descending alignment order in the layout. -/
syntax (name := transmogLayoutOrder.auto) &"auto" : transmogLayoutOrder

/-- Layout alignment. -/
declare_syntax_cat transmogLayoutAlign (behavior := symbol)
/-- Caps each field's alignment at the given power of two, defaulting to 1. -/
syntax (name := transmogLayoutAlign.packed) &"packed" (num)? : transmogLayoutAlign
/-- Raises the struct alignment to at least the given power of two. -/
syntax (name := transmogLayoutAlign.align) &"align" num : transmogLayoutAlign

/-- Layout specification. -/
syntax transmogLayoutSpec := transmogLayoutOrder transmogLayoutAlign

/-- Deriving layout based on the representation. -/
syntax transmogDeriveLayout := &"derive_layout " transmogLayoutSpec,+

/--
Replacing the runtime representation of the type by the packed representation word.

The clause must appear in the module that declares the type, and that module must re-export a
path to the Transmog code generator passes, which `public import Transmog.DSL` provides.

This is experimental and relies on how the current Lean compiler lowers inductive types.  The
carrier can be given explicitly with `replace_runtime as UInt16`, choosing one of `UInt8`,
`UInt16` and `UInt32`; by default the smallest one that fits the representation is used.

A structure, or an inductive whose every constructor carries a field, is accepted only under
`transmog.replaceRuntime.overrideClassification`, which makes the clause override the compiler's
IR classification of the type; see the option's description.
-/
syntax transmogReplaceRuntime := &"replace_runtime" (&" as " ident)?

open Lean Parser Tactic in
/-- Manual proof for the `toRepr`/`fromRepr` round-trip. -/
syntax transmogCorrectBy := &"correct_by " tacticSeqIndentGt

syntax transmogSuffixes :=
  (ppDedent(ppLine) transmogReplaceRuntime)?
  (ppDedent(ppLine) transmogDeriveLayout)?
  (ppDedent(ppLine) transmogCorrectBy)?

/--
Declare data representation for a Lean type.  A data representation is an array of unsigned integer
types, possibly with some constraints, that can represent a value of the type.  Namely, any value of
the type can be converted to (i.e., represented by) the array of unsigned integer types, and
conversely we can recover the original value from a given array of unsigned integer types, as
declared.  A data representation is encoded in the `DataRepr` type class, with `DataRepr.toRepr` and
`DataRepr.fromRepr` encoding the conversion, and `DataRepr.from_to` a proof that after `toRepr` then
`fromRepr`, we get the same original value.

Example:
```lean
inductive Num where
  | zero
  | nonzero (n : { x : UInt32 // x ≠ 0 })

transmog Num as [r : UInt32] where
  | zero => guard r = 0
  | nonzero =>
    n : { x : UInt32 // x ≠ 0 } <= r
```

A type with parameters is represented one instantiation at a time, by applying it to its
arguments, as in `transmog Node Ptr as [n : UInt32[0:31]] where ...` for `Node (α : Type u)`.  The
type is written as a head applied to arguments of maximal precedence, so a compound argument is
parenthesised, as in `transmog Option (Option Bool) as ...`.  The representation then belongs to
that instantiation alone, each instantiation gets its own instance, and field types are written as
they are after instantiation, as in `p : Ptr <= n` for a constructor field of type `α`.  A bare
type `T` also receives the package `T.Repr` holding `toRepr`, `fromRepr` and `from_to`, whereas an
instantiation has no namespace of its own and is reached through `DataRepr` and `HasLayout`.
Indexed families are not supported, and `replace_runtime` does not apply to an instantiation,
since the compiler represents an inductive type the same way for all of them.  A closed type can
also be declared together with its representation, by `transmog enum` and `transmog struct`
below.

A field whose type has a representation is placed through it.  When the carrier of that
representation is a subtype of the slot's scalar, the slot's constraints and the guards must
establish the carrier's predicate for every slot value that reaches the field, and the predicate
is in turn available to the proofs.  A slot value that no field's encoding produces is free to
mark a constructor, which keeps an `Option Bool` in one byte.
```lean
transmog Option Bool as [r : UInt8 // r ≤ 2] where
  | none => guard r = 2
  | some => val : Bool <= lsbAsBool r
```
On top of it, `Option (Option Bool)` is represented the same way at `[r : UInt8 // r ≤ 3]`, with
`guard r = 3` and `val : Option Bool <= r`.

Normally, the `DataRepr.from_to` proof is automatically discharged if the declaration is valid and
contains enough information.  If it fails, a `correct_by` clause can be supplied to give a manual
proof instead.

When the `replace_runtime` clause is given, also replace the runtime representation of the type by
the packed representation word, so that values of the type are boxed machine words rather than
heap-allocated constructor objects.  This is experimental; see the module documentation for its
preconditions and its trust story.

When the `derive_layout` clause is given, also derive data layout for the type based on the
declared representation.  A data layout maps the data representation to a potentially larger one,
with the extra slots being padding slots.  A data layout is encoded as a `Layout` value, and can be
looked up using the `HasLayout` type class.
-/
syntax (name := transmogRepr)
  "transmog " notFollowedBy(&"enum" <|> &"struct") (notFollowedBy(&"as") term:max)+ &" as "
    transmogReprSpec (" where " transmogReprBody)? (transmogSuffixes)? : command

/-!
## The combined declaration forms

`transmog enum` and `transmog struct` declare a type and its representation in one command.  The
constructors and the fields are written once, in the shape the `inductive` and `structure`
commands take, with each field carrying its place.  The keywords `enum` and `struct` are not
reserved, which is why the standalone form above refuses them as the head of the type.
-/

/--
A constructor field of a `transmog enum` declaration, a binder that also gives the field's place,
as in `(p : Ptr <= n)`.
-/
syntax transmogCtorField := "(" ident " : " term:51 " <= " transmogReprFieldValue ")"

/-- Slot hints, one per line. -/
syntax transmogReprHints :=
  manyIndent(ppLine notFollowedBy(transmogClauseKeyword) transmogReprHint)

/-- The guard and the slot hints of a constructor of a `transmog enum` declaration. -/
syntax transmogCtorTail := " => " (transmogReprGuard)? transmogReprHints

/--
A constructor of a `transmog enum` declaration, in the shape of a constructor of an `inductive`
whose fields carry their places.  The doc comment and the modifiers belong to the constructor of
the generated `inductive`, and the guard and the slot hints of its arm follow a `=>`.

Example:
```lean
| sink => guard n = 0
| inode (p : Ptr <= n)
```
-/
syntax transmogEnumCtor :=
  ppIndent(ppLine atomic((docComment)? "| ") nestedDeclModifiers ident (ppSpace transmogCtorField)*
    (transmogCtorTail)?)

/-- A field of a `transmog struct` declaration with its place, or a slot hint. -/
declare_syntax_cat transmogStructWrite
/--
A field of a `transmog struct` declaration, in the shape of a field of a `structure` that also
gives the field's place, as in `node : Node <= r[1:32]`.  The doc comment and the modifiers
belong to the field of the generated `structure`, and so does the default value or the
auto-param that may follow the place, as in `compl : Bool <= lsbAsBool r[0] := false`.
-/
syntax (name := transmogStructWrite.field)
  atomic(nestedDeclModifiers ident) " : " term:51 " <= " transmogReprFieldValue
    (Lean.Parser.Term.binderTactic <|> Lean.Parser.Term.binderDefault)? : transmogStructWrite
syntax (name := transmogStructWrite.hint) transmogReprHint : transmogStructWrite

syntax transmogStructFields :=
  manyIndent(ppLine notFollowedBy(transmogClauseKeyword) transmogStructWrite)

/--
The instances to derive for the declared type.  They are derived right after the type, before the
representation, which may use them, as the fallback branch of `fromRepr` uses `Inhabited` and a
`correct_by` proof may use `DecidableEq`.  When a `replace_runtime` clause is present they are
derived last instead, so they are compiled against the runtime representation the clause
installs.
-/
syntax transmogDeriving :=
  ppDedent(ppLine) atomic("deriving " notFollowedBy("instance") notFollowedBy("noncomputable"))
    Lean.Parser.Command.derivingClasses

/--
Declare an inductive type together with its data representation.

Example:
```lean
transmog enum Node as [n : UInt32[0:31]] where
  | sink => guard n = 0
  | inode (p : Ptr <= n)
replace_runtime
deriving DecidableEq, Repr
```
declares `inductive Node` with the constructors `sink` and `inode (p : Ptr)`, then the
representation `transmog Node as [n : UInt32[0:31]] where ...` with the same constructors, in
which the field `p` is placed at `n`, and finally derives the instances.  Everything written on
the type and on its constructors goes to the `inductive` unchanged, namely the doc comment, the
attributes and the visibility of the type, and the doc comment and the modifiers of each
constructor.  The `=>` block of a constructor holds the guard and the slot hints of its arm.
The clauses of a `transmog` declaration follow the constructors, and the `deriving` clause comes
last.  Its instances are derived right after the type, so the representation can use them, unless
a `replace_runtime` clause is present, in which case they are derived after the clause has taken
effect.

The type has no parameters, universe parameters or indices, since a representation belongs to a
closed type, and it is neither `unsafe` nor `meta`, since the generated definitions and the
round-trip theorem are ordinary declarations.  An instantiation of a parametric type declared
elsewhere is represented with the standalone `transmog` declaration.
-/
syntax (name := transmogEnum)
  declModifiers "transmog " &"enum " ident &" as " transmogReprSpec " where "
    (transmogEnumCtor)+ (transmogSuffixes)? (transmogDeriving)? : command

/--
Declare a structure together with its data representation.

Example:
```lean
transmog struct Edge as [r : UInt32] where
  compl : Bool <= lsbAsBool r[0]
  node : Node <= r[1:32]
derive_layout C packed
deriving DecidableEq, Repr
```
declares `structure Edge` with the fields `compl : Bool` and `node : Node`, then the
representation `transmog Edge as [r : UInt32] where ...` placing them, and finally derives the
instances.  A field keeps the doc comment, the modifiers, the default value and the auto-param a
`structure` field takes, and a custom constructor is declared before the fields, as in
`make ::`.  A line `place := value` among the fields is a slot hint.  The restrictions of
`transmog enum` apply, and `extends` is not supported.
-/
syntax (name := transmogStruct)
  declModifiers "transmog " &"struct " ident &" as " transmogReprSpec " where "
    (Lean.Parser.Command.structCtor)? transmogStructFields (transmogSuffixes)? (transmogDeriving)?
    : command

end Transmog

end -- public meta section
