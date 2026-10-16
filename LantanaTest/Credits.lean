module

public import Lantana

/-! Universe check for transfinite later credits: a closed world `TestGF : BundledGFunctors.{0}`
with the ordinal credit ghost state in a slot, its `TlcGpreS` instance, and a proof that
allocates credits and splits them.

Universe annotations that were necessary:
- `IProp TestGF : TypeSI 0 = Type 4`, so every slot is a functor with results in `Type 4`.
  The credit camera `Auth Ordinal.{1}` is in `Type 2`, so the slot is
  `ULiftOF.{4} (CreditF Ordinal.{1})`. The level `4` of `ULiftOF` must be written: Lean cannot
  solve `max 2 ?w = 4`.
- `constOF` of Iris-Lean takes `B : Type`; `Ordinal.{1} : Type 2` needs the
  universe-polymorphic `Lantana.constOFP` (inside `CreditF`). Its argument universes are
  inferred from the slot type.
- The instance is `(ElemG.ofEq 0 rfl).ofLift`; `ElemG.ofEqLift` only accepts functors with
  results in `Type`.
- `Ordinal.{1}` is written with its universe in the slot and wherever a numeral or `+ₕ` term
  is not otherwise constrained (an unannotated `1 : Ordinal` gets a universe metavariable). -/

namespace LantanaTest.Credits

open Iris Lantana Ordinals Ordinal

noncomputable def TestGF : BundledGFunctors.{0} := fun n =>
  match n with
  | 0 => ⟨ULiftOF.{4} (CreditF Ordinal.{1}), by infer_instance⟩
  | _ => ⟨constOFU Unit, by infer_instance⟩

noncomputable instance : TlcGpreS TestGF where
  elem := (ElemG.ofEq 0 (by unfold TestGF; rfl)).ofLift

/-- Split `£ₒ (1 +ₕ 1)` with the `IntoSep` instance for `+ₕ`. -/
theorem split_two [TlcGS TestGF] :
    £ₒ (1 +ₕ 1 : Ordinal.{1}) ⊢@{IProp TestGF} £ₒ (1 : Ordinal.{1}) ∗ £ₒ (1 : Ordinal.{1}) := by
  iintro ⟨H1, H2⟩
  iframe

/-- Allocate the credit ghost state with two credits and split them. The ghost state `G` that
`%G` introduces is not a local instance of the proof mode, so it is passed explicitly. -/
example : ⊢@{IProp TestGF} |==> ∃ _ : TlcGS TestGF,
    ●£ₒ (1 +ₕ 1 : Ordinal.{1}) ∗ £ₒ (1 : Ordinal.{1}) ∗ £ₒ (1 : Ordinal.{1}) := by
  imod credit_alloc (1 +ₕ 1 : Ordinal.{1}) with ⟨%G, Hs, H⟩
  iexists G
  imodintro
  iframe Hs
  iapply @split_two G $$ H

/-- Two credits pay for two laters. -/
example [TlcGS TestGF] (P : IProp TestGF) : £ₙ 2 ∗ ▷ ▷ (|==>r P) ⊢@{IProp TestGF} |==>r P := by
  iintro ⟨H, HP⟩
  icases (tlc_split_nat 1 1).mp $$ H with ⟨H1, H2⟩
  iapply tlc_later
  isplitl [H1]
  · iexact H1
  inext
  iapply tlc_later
  isplitl [H2]
  · iexact H2
  iexact HP

/-- A transfinite step: `£ₒ ω` pays for one later and leaves any finite number of credits. -/
example [TlcGS TestGF] (P : IProp TestGF) (n : Nat) :
    £ₒ ω ∗ (£ₙ n -∗ ▷ |==>r P) ⊢@{IProp TestGF} |==>r P :=
  tlc_later_strong (ofNat_lt_omega n)

/-- `ALC` allocates a credit to strip a later. -/
example [TlcGS TestGF] (P : IProp TestGF) : ALC iprop(▷ P) ⊢ ALC P :=
  ALC_later.mpr

/-- The proof mode eliminates basic and relational updates in front of `|==>r`. -/
example [TlcGS TestGF] (P Q : IProp TestGF) :
    (|==> P) ∗ (|==>r Q) ⊢@{IProp TestGF} |==>r (P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  imod HP
  imod HQ
  imodintro
  iframe

end LantanaTest.Credits
