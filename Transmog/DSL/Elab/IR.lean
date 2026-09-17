/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.Elab.Command
public meta import Transmog.DSL.Notation

/-!
# Transmog elaboration IR

The intermediate representation between the `transmog` surface syntax and the emitted definitions.
The IR reflects logical roles, not surface shapes:

- `Slot` keeps user-written `//` properties (`userProps`) separate from the range-derived
  `fitsBits` property, which is recomputable via `fitsProp?`.
- Values are `CheckedValue` trees: the syntax walk resolves each leaf's `FieldConversion` and
  support requirement once (`ToIR.toCheckedValue`), so the emitters are plain syntax folds with
  no elaboration and no threaded `insideCast` state.
- Transformation gadgets form the closed `Gadget` inductive; each gadget is interpreted in
  exactly one place per direction in the emitters.
- Every representation body is an array of `Arm`s: a structure is the degenerate case of a
  single unguarded arm for the structure constructor, so the emitters need no struct/enum fork.
-/

public meta section

namespace Transmog.DSL

open Lean

def getUIntBitWidth? : Name → Option Nat
  | ``UInt8 => some 8
  | ``UInt16 => some 16
  | ``UInt32 => some 32
  | ``UInt64 => some 64
  | _ => none

/-- A half-open bit interval `[start, stop)` inside a scalar slot. -/
structure BitRange where
  start : Nat
  stop : Nat
deriving Inhabited, Repr

/-- A reference to (a bit range of) a representation slot. -/
structure Place where
  name : Ident
  slotIdx : Nat
  range? : Option BitRange := none
deriving Inhabited

/--
A representation slot: a scalar-typed physical field of the representation.  `ty` is the resolved
scalar constant, spliced into generated code with `mkCIdent`.  `range?` restricts the usable
bits, inducing a `fitsBits` subtype; `userProps` holds only the user-written `//` properties,
with the range-derived property recomputable via `fitsProp?`.
-/
structure Slot where
  name : Ident
  ty : Name
  width : Nat
  range? : Option BitRange := none
  userProps : Array Term := #[]
deriving Inhabited

/-- The range-induced `fitsBits` property of a slot, if the slot is ranged. -/
def Slot.fitsProp? (slot : Slot) : Option Term :=
  slot.range?.map fun range =>
    Syntax.mkApp (mkCIdent (slot.ty ++ `fitsBits))
      #[⟨Syntax.mkNatLit (range.stop - range.start)⟩, slot.name]

/--
All properties constraining a slot's value: the user-written ones, then the range-induced
`fitsBits`.
-/
def Slot.allProps (slot : Slot) : Array Term :=
  match slot.fitsProp? with
  | .some fits => slot.userProps.push fits
  | .none => slot.userProps

/-- The slot type as a term: the bare scalar, or the subtype over `allProps` when constrained. -/
def Slot.mkType [Monad m] [MonadQuotation m] (slot : Slot) : m Term := do
  let ty := mkCIdent slot.ty
  match slot.allProps with
  | #[] => pure ty
  | props =>
    let prop ← props.pop.foldrM (init := props.back!) fun p acc =>
      `(($p:term) ∧ ($acc:term))
    `({ $slot.name:ident : $ty:ident // $prop:term })

/-- The element type of a place: the bare scalar, or the range-induced `fitsBits` subtype. -/
def mkSlotElemTy [Monad m] [MonadQuotation m] (slotTy : Name) (range? : Option BitRange) :
    m Term := do
  let ty := mkCIdent slotTy
  match range? with
  | .none => pure ty
  | .some range =>
    let width : TSyntax `num := ⟨Syntax.mkNatLit (range.stop - range.start)⟩
    let fitsBits := mkCIdent (slotTy ++ `fitsBits)
    `({ x : $ty:ident // $fitsBits $width:num x })

/--
Structural classification of the conversion between a field's declared type `α` and its
slot-side value type `β`.  With `γ_α`/`γ_β` the `whnfR` `Subtype` base (or the type itself), the
table is:

| kind | condition | toRepr | fromRepr |
|---|---|---|---|
| `equiv` | `α ≡ β` | `f` | `s` |
| `project` | `α` Subtype over `γ ≡ β` | `f.val` | `⟨s, _⟩` |
| `inject` | `β` Subtype over `γ ≡ α` | `⟨f, _⟩` | `s.val` |
| `reproject` | both Subtypes, `γ_α ≡ γ_β` | `⟨f.val, _⟩` | `⟨s.val, _⟩` |
| `reprProject` | `DataRepr α ρ`, `ρ` Subtype over `γ ≡ β` | `(toRepr f).val` | `fromRepr ⟨s, _⟩` |
| `reprReproject` | `DataRepr α ρ`, `ρ` and `β` Subtypes, `γ_ρ ≡ γ_β` | `⟨(toRepr f).val, _⟩` | `fromRepr ⟨s.val, _⟩` |
| `needCast` | otherwise | `DataCastT.castTo` | `DataCastT.castFrom` |

The `⟨_, _⟩` obligations are discharged by `transmog_subtype`, with the source value's
`.property` injected as a local hypothesis where codegen has it at hand.  The two
representation rows place a field that is not itself a `Subtype` through its representation
carrier `ρ`, when that carrier is a `Subtype` other than `β`; a carrier that is `β` itself
converts through the identity `DataCastT`.  An explicit DSL `cast` bypasses the table and
forces `DataCastT`.
-/
inductive FieldConversion where
  | equiv
  | project
  | inject
  | reproject
  | reprProject
  | reprReproject
  | needCast
deriving Inhabited

/-- Whether the conversion goes through the `DataRepr` instance of the field type. -/
def FieldConversion.viaRepr : FieldConversion → Bool
  | .reprProject | .reprReproject => true
  | _ => false

/-- A value transformation gadget applied on top of another value. -/
inductive Gadget where
  /--
  Convert through a lawful `DataCastT` instance; the inner value converts with no
  classification of its own.
  -/
  | cast
  /-- View the least significant bit of an atomic place as a `Bool`. -/
  | lsbAsBool
deriving Inhabited

/--
A checked field value tree.  The conversion and support annotations are resolved during the
`ToIR` pass, against the field's declared type; the emitters fold over this tree purely.
-/
inductive CheckedValue where
  /--
  A slot place; `conv` converts between the field-side factor type and the place's element
  type, and `needsProperty` records whether the round-trip proof should inject a property,
  that of the field-side factor when it is a `Subtype`, and that of its representation when
  the conversion goes through one.
  -/
  | place (conv : FieldConversion) (needsProperty : Bool) (p : Place)
  /--
  A gadget applied to an inner value.  For `.cast` the inner tree carries no conversions;
  for `.lsbAsBool` the inner tree is an atomic place and `conv` classifies against `Bool`.
  -/
  | transform (g : Gadget) (conv : FieldConversion) (needsProperty : Bool)
      (inner : CheckedValue)
  /-- A product of component values, matched factor-wise against the field type. -/
  | prod (components : Array CheckedValue)
deriving Inhabited

/-- A logical field of the source type and the checked value it decodes from. -/
structure Field where
  name : Ident
  ty : Term
  val : CheckedValue
deriving Inhabited

/-- A slot write: `value` is assigned to (the range of) `place` in the `toRepr` direction. -/
structure Write where
  place : Place
  value : Term
deriving Inhabited

/-- A decoding guard together with the writes inferred from its assertions. -/
structure Guard where
  cond : Term
  writes : Array Write
deriving Inhabited

/--
The representation of one constructor.  A structure declaration normalizes to a single
unguarded arm for the structure constructor, so emitters treat all bodies uniformly.
-/
structure Arm where
  /-- The constructor as the user named it, for messages and hovers. -/
  ctor : Ident
  /-- The constant of the constructor. -/
  ctorName : Name
  guard? : Option Guard := none
  /-- The constructor payload fields, in constructor argument order. -/
  fields : Array Field
  /-- Explicit slot write hints (`place := value`). -/
  hints : Array Write := #[]
deriving Inhabited

/--
A checked `transmog` declaration.  `sourceRef` is the type as written, `sourceExpr` its elaboration,
a constant applied to its arguments, and `sourceName` that constant.  `arms?` is `none` for a
type-alias repr.
-/
structure ReprDecl where
  sourceRef : Term
  sourceExpr : Expr
  sourceName : Name
  slots : Array Slot
  arms? : Option (Array Arm) := none
deriving Inhabited

end Transmog.DSL

end -- public meta section
