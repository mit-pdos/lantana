/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.GhostVar
public import Lantana.Examples.Lib

/-! # A handoff cell

Rocq `examples/handoff.v`: `send b f a` puts a task `f a` into the cell `b`, and `receive b`
waits for a task and runs it. A task comes with the obligations `K` it discharges, and its
specification `taskAt ℓt μ P f a K` is a higher-order one (an `lWP` triple, stored in the
invariant); `isTask ℓ f a K` hides the layer `ℓt < ℓ` of its fuel and its resource `P`.

The receiver's thread owns an inbox obligation `g` (layer `0`, no children). The invariant
`handoffInv` holds the cell's state and the current inbox (a ghost variable, half of it with the
receiver): empty, or a task waiting in a container `c` below the inbox, or taken.

* `send` creates the container `c` below the inbox (`Obl.new` under an obligation, with
  `parLe_obl`) at the task's layer `ℓt`, and moves the task's obligations `K` from their parent
  into it (`obl_move_obl_set`, paying one unit each at the layer `ℓ > ℓt`). Measure `20`.
* `receive` is proved by Löb induction over the inbox (`iloeb`): spinning on the empty cell is
  paid by the inbox's fuel, and the inbox is renewed at every iteration (the old one is
  discharged, a new one is created with fresh fuel, `Obl.new` below the thread), so each inbox
  sees finitely many steps; with a task, the container moves up to the thread (`Obl.move_up`),
  the inbox is discharged, and the task runs with the container's fuel (`taskAt`), after which
  the container is discharged. Measure `10` (a task brings its own fuel). One later credit per
  iteration opens the invariant and strips the later of the induction hypothesis at once.

The guarantee `guar_isHandoff`: always, the cell holds `NONE` or a task (`handoffTr`, through
`handoffInvTrSpec_ext`); the location's value is trace-visible (an existential over `Val`), the
inbox and the obligations are ghost.

Everything here is proved, from the obligation-forest interface and the rules of temporal
formulas (whose own proofs are M4–M6).
-/

@[expose] public noncomputable section

namespace Lantana.Examples.Handoff

open Iris Iris.BI Lantana Lantana.HeapLang Lantana.Language
open scoped Lantana.TrSpec Lantana.TrProp Lantana.Measure Ordinals.Ordinal

/-! ## The program -/

/-- `λ b f a, b ← some (f, a)`. -/
@[lantana_alias Handoff.send]
def send : Val := hl_val(λ b f a, b ← some((f, a)))

/-- `rec loop b := match !b with none => loop b | some x => (fst x) (snd x)`. -/
@[lantana_alias Handoff.receive]
def receive : Val :=
  hl_val(rec loop b := match !b with | none() => loop b | some(x) => (fst(x)) (snd(x)))

/-- The empty cell. -/
def vNone : Val := hl_val(none())

/-- The cell holding the task `f a`. -/
def vSome (f a : Val) : Val := hl_val(some((&f, &a)))

/-- The unit value. -/
def vUnit : Val := hl_val(#())

/-- The namespaces of the handoff and of its invariant. -/
def N : Namespace := nroot.@"handoff"
def Na : Namespace := N.@"always"

/-! ## Ghost state -/

/-- The camera of the handoff: a ghost variable holding the receiver's current inbox. -/
@[lantana_alias handoffG]
class HandoffG (GF : BundledGFunctors) where
  [ghostVar : GhostVarG GF Oid]

attribute [reducible, instance] HandoffG.ghostVar

#lantana_ignore handoffGpreS "The camera has no ghost names: `HandoffG` serves before allocation."
#lantana_ignore «handoffΣ» "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."
#lantana_ignore «subG_handoffΣ» "Subsumed by the `BundledGFunctors` worlds (`Examples.ExGF`)."

/-- The ghost name of a handoff. -/
@[lantana_alias handoff_γ]
structure HandoffName where
  /-- The ghost variable of the inbox. -/
  γd : GName

attribute [lantana_alias HandoffName] HandoffName.mk
attribute [lantana_alias handoff_γd] HandoffName.γd

/-! ## Halves of the ghost variable -/

section GhostVar
variable {GF : BundledGFunctors} [HandoffG GF]

/-- A ghost variable is two halves. -/
theorem ghostVar_halves (γ : GName) (a : Oid) :
    (γ ↪VAR a) ⊢@{IProp GF} (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR{.own (1 : Qp).half} a) := by
  have h := ghost_var_split (GF := GF) γ a (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iintro H
  iapply h $$ H

/-- Two halves of a ghost variable agree, and make the whole. -/
theorem ghostVar_combine_halves (γ : GName) (a b : Oid) :
    (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR{.own (1 : Qp).half} b) ⊢@{IProp GF}
      (γ ↪VAR a) ∗ ⌜a = b⌝ := by
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_agree γ a _ b _ $$ H1 H2
  subst h
  icombine H1 H2 as H
  iframe H
  ipureintro
  rfl

/-- A half and a whole of a ghost variable are incompatible. -/
theorem ghostVar_half_whole_false (γ : GName) (a b : Oid) :
    (γ ↪VAR{.own (1 : Qp).half} a) ∗ (γ ↪VAR b) ⊢@{IProp GF} False := by
  iintro ⟨H1, H2⟩
  ihave %⟨h, -⟩ := ghost_var_valid_2 γ a _ b _ $$ H1 H2
  have := DFrac.valid_op_own h
  simp at this

end GhostVar

/-! ## The invariant -/

section Invariant
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [HandoffG GF]

/-- A task `f a` that discharges the obligations `K`, using fuel at layer `ℓt` for the children
of the running thread. The obligations `K` are children of some parent `p`. -/
@[lantana_alias task_at]
def taskAt (ℓt : Layer) (μ : Measure) (P : IProp GF) (f a : Val) (K : Oids) : IProp GF :=
  iprop(∀ (lc : Fuel) (i : ThreadId) (G : Oids) (p : Parent) (K' : Oids) (C : List ECtxItem),
    l{{{ threadExpr i C hl(v(&f) v(&a)) ∗ thKids i G ∗ ([∗set] g ∈ G, Obl.fuel g ℓt μ) ∗
          Par.kids p K' ∗ ⌜K ⊆ K'⌝ ∗ P }}}
        hl(v(&f) v(&a)) @ i
      l{{{ (rv : Val), RET rv; threadExpr i C hl(&rv) ∗ £ₒ lc ∗ thKids i G ∗
        Par.kids p (K' \ K) }}})

instance taskAt_persistent (ℓt : Layer) (μ : Measure) (P : IProp GF) (f a : Val) (K : Oids) :
    Persistent (taskAt ℓt μ P f a K) := by
  unfold taskAt; infer_instance

/-- A task below the layer `ℓ`: its fuel is at a layer `ℓt < ℓ`, and it needs the resource
`P`. -/
@[lantana_alias is_task]
def isTask (ℓ : Layer) (f a : Val) (K : Oids) : IProp GF :=
  iprop(∃ (ℓt : Layer) (P : IProp GF), ⌜ℓt < ℓ⌝ ∧ (P ∗ ∃ μ : Measure, taskAt ℓt μ P f a K))

/-- The receiver `g`'s inbox. A sent task waits in a container `c` below the inbox, at the
layer `ℓt` of the task's fuel; `c` holds the task's obligations and the fuel of the receiver for
running it. -/
@[lantana_alias handoff_task]
def handoffTask (g : Oid) (ℓ : Layer) (f a : Val) (K : Oids) : IProp GF :=
  iprop(∃ (c : Oid) (ℓt : Layer) (μ : Measure) (P : IProp GF),
    oblKids g {c} ∗ oblKids c K ∗ Obl.assigned c 1 ∗ Obl.fuel c ℓt (μ + 10) ∗ ⌜ℓt < ℓ⌝ ∗ P ∗
      taskAt ℓt μ P f a K)

/-- The cell is empty (and the receiver's inbox `g` has no children), or it holds a task sent
to the inbox, or a task the receiver has taken. -/
@[lantana_alias handoff_inv]
def handoffInv (b : Loc) (γd : GName) (ℓ : Layer) : IProp GF :=
  iprop(∃ g : Oid,
    (b ↦{.own (1 : Qp).half} some vNone ∗ (γd ↪VAR{.own (1 : Qp).half} g) ∗ oblKids g ∅ ∗
      Wit.layer g 0) ∨
    (∃ (f a : Val) (K : Oids), b ↦ some (vSome f a) ∗ (γd ↪VAR{.own (1 : Qp).half} g) ∗
      handoffTask g ℓ f a K) ∨
    (∃ f a : Val, b ↦ some (vSome f a) ∗ (γd ↪VAR g)))

/-- The handoff `b` (persistent). -/
@[lantana_alias is_handoff]
def isHandoff (b : Loc) (γ : HandoffName) (ℓ : Layer) : IProp GF :=
  alwaysI Na (handoffInv b γ.γd ℓ)

@[lantana_alias handoff_inv_persistent]
instance isHandoff_persistent (b : Loc) (γ : HandoffName) (ℓ : Layer) :
    Persistent (isHandoff (GF := GF) b γ ℓ) := by
  unfold isHandoff; infer_instance

/-- What the handoff exports: the cell always holds `NONE` or a task `SOME (f, a)`; the task's
resources and the obligations have no trace content. -/
@[lantana_alias handoff_inv_trSpec]
def handoffInvTrSpec (b : Loc) : TrSpec Exp State GF :=
  (TrSpec.state (pointstoSat b (.own (1 : Qp).half) vNone) ∧ₛ TrSpec.true) ∨ₛ
    (∃ₛ (f : Val) (a : Val), TrSpec.state (pointstoSat b (.own 1) (vSome f a)) ∧ₛ
      TrSpec.true) ∨ₛ
    (∃ₛ (f : Val) (a : Val), TrSpec.state (pointstoSat b (.own 1) (vSome f a)) ∧ₛ
      TrSpec.true)

theorem guar_handoffInv (b : Loc) (γd : GName) (ℓ : Layer) :
    ⊢@{IProp GF} handoffInv b γd ℓ ⊨ₜ handoffInvTrSpec b := by
  unfold handoffInv handoffInvTrSpec
  iapply guar_ex_ghost
  iintro %g
  iapply guar_or
  · iapply guar_sep
    · iapply (GuarOf.guar_of (P := b ↦{.own (1 : Qp).half} some vNone))
    · iapply guar_true
  iapply guar_or
  · iapply guar_ex
    iintro %f
    iapply guar_ex
    iintro %a
    iapply guar_ex_ghost
    iintro %K
    iapply guar_sep
    · iapply (GuarOf.guar_of (P := b ↦ some (vSome f a)))
    · iapply guar_true
  · iapply guar_ex
    iintro %f
    iapply guar_ex
    iintro %a
    iapply guar_sep
    · iapply (GuarOf.guar_of (P := b ↦ some (vSome f a)))
    · iapply guar_true

@[lantana_alias guar_is_handoff]
theorem guar_isHandoff (b : Loc) (γ : HandoffName) (ℓ : Layer) :
    ⊢@{IProp GF} isHandoff b γ ℓ ⊨ₜ □ₛ handoffInvTrSpec b := by
  haveI : GuarOf (handoffInv (GF := GF) b γ.γd ℓ) (handoffInvTrSpec b) :=
    ⟨guar_handoffInv b γ.γd ℓ⟩
  unfold isHandoff
  exact IntoGuar.into_guar

/-- The invariant is registered: a model update. The inbox `g` is an obligation at layer `0`
without children. -/
@[lantana_alias is_handoff_initialize]
theorem isHandoff_initialize (E : CoPset) (b : Loc) (ℓ : Layer) (g : Oid) :
    b ↦{.own (1 : Qp).half} some vNone ⊢ oblKids g ∅ -∗ Wit.layer g 0 -∗
      |={E}=>m ∃ γ : HandoffName, isHandoff (GF := GF) b γ ℓ ∗
        (γ.γd ↪VAR{.own (1 : Qp).half} g) := by
  iintro Hb Kg #Wg
  imod ghost_var_alloc g with ⟨%γ, Gv⟩
  icases ghostVar_halves γ g $$ Gv with ⟨Gv, Gv0⟩
  imod alwaysI_alloc (E := E) (N := Na) (P := handoffInv b γ ℓ) $$ [Hb Kg Gv] with #HA
  · inext
    unfold handoffInv
    iexists g
    ileft
    iframe
    iexact Wg
  imodintro
  iexists ⟨γ⟩
  iframe Gv0
  unfold isHandoff
  iexact HA

end Invariant

/-! ## Specifications -/

section Specs
variable {GF : BundledGFunctors} [ModelGS GF] [HeapGS GF] [HandoffG GF]

/-- Sending a task: its obligations `K` move from their parent `p` into a new container below
the receiver's inbox, each paying one unit of fuel at the layer `ℓ` above the task's. -/
@[lantana_alias Handoff_send_spec]
theorem send_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (b : Loc) (f a : Val) (G : Oids)
    (p : Parent) (K K' : Oids) (γ : HandoffName) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&send) #b v(&f) v(&a)) ∗ thKids i G ∗
          ([∗set] g ∈ G, Obl.fuel g 0 μ) ∗ Par.kids p K' ∗ ⌜K ⊆ K'⌝ ∗
          ([∗set] k ∈ K, Obl.fuel k ℓ 1) ∗ b ↦{.own (1 : Qp).half} some vNone ∗
          isTask ℓ f a K ∗ isHandoff b γ ℓ }}}
        hl(v(&send) #b v(&f) v(&a)) @ i
      l{{{ RET vUnit; threadExpr i C hl(#()) ∗ £ₒ lc ∗ thKids i G ∗ Par.kids p (K' \ K) }}} := by
  refine ⟨20, fun lc i b f a G p K K' γ ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, HK, %hK, HFK, Hb, Htask, #Hh⟩ HΦ
  ihave HF := oblFuels_init G 20 0 $$ HF
  unfold send
  lwp_step HT HG HF with Hlc : lc +ₕ 1
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  lwp_expr_simp
  lwp_step HT HG HF
  lwp_step HT HG HF
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  icases oblFuels_add 1 12 G $$ HF with ⟨HF1, -⟩
  unfold isHandoff
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := handoffInv b γ.γd ℓ)
    (fun _ _ => CoPset.mem_full) $$ Hh
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold handoffInv
  icases Hinv with ⟨%g, (⟨Hb0, Gv, Kg, #Wg⟩ | ⟨%f', %a', %K'', Hb0, -⟩ | ⟨%f', %a', Hb0, -⟩)⟩
  · icombine Hb Hb0 as Hb
    iapply lwp_store (o := 0) (C := C) (G := G) (R := ∅) $$ [HT HG HF1 Hb]
    · iframe HT Hb
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Hb⟩
    -- The container of the task, below the inbox at the layer of the task's fuel.
    unfold isTask
    icases Htask with ⟨%ℓt, %P, %hlt, HP, %μ, #Task⟩
    imod Obl.new (⊤ \ ↑Na) (.obl g) ∅ ℓt (μ + 10) $$ [] Kg with ⟨%c, -, Kg, Kc, Ac, Fc, #Wc⟩
    · iapply parLe_obl (ℓq := 0) g (Ordinals.Ordinal.zero_le ℓt) $$ Wg
    imod obl_move_obl_set (⊤ \ ↑Na) p c K' ∅ K ℓt hK $$ Wc HK Kc [HFK] with ⟨-, HK, Kc⟩
    · iapply BigSepS.bigSepS_impl $$ HFK
      imodintro
      iintro %k %_ Hk
      iexists ℓ
      iframe Hk
      ipureintro
      exact hlt
    imod Hclose $$ [Hb Gv Kg Kc Ac Fc HP]
    · unfold vSome
      inext
      iexists g
      iright
      ileft
      iexists f, a, K
      iframe Hb Gv
      unfold handoffTask
      iexists c, ℓt, μ, P
      iframe Ac Fc HP
      isplitl [Kg]
      · iapply Par.kids_congr _ $$ Kg
        intro z
        simp
      isplitl [Kc]
      · iapply Par.kids_congr _ $$ Kc
        intro z
        simp
      isplitr
      · ipureintro
        exact hlt
      · iexact Task
    imodintro
    rw [show (hl_val(#()) : Val) = vUnit from rfl]
    iapply HΦ
    iframe
  · iexfalso
    ihave %h := pointsTo_agree (l := b) $$ [Hb Hb0]
    · iframe
    simp [vNone, vSome] at h
  · iexfalso
    ihave %h := pointsTo_agree (l := b) $$ [Hb Hb0]
    · iframe
    simp [vNone, vSome] at h

/-- Receiving: the receiver spins on the cell with the fuel of its inbox `g`, which it renews
at every iteration; once a task has been sent, it runs it with the fuel of the task's
container. The loop is not claimed to terminate (with nothing sent it spins forever). -/
@[lantana_alias Handoff_receive_spec]
theorem receive_spec : ∃ μ : Measure, ∀ (lc : Fuel) (i : ThreadId) (b : Loc) (g : Oid)
    (γ : HandoffName) (ℓ : Layer) (C : List ECtxItem),
    ⊢@{IProp GF} l{{{ threadExpr i C hl(v(&receive) #b) ∗ thKids i {g} ∗
          ([∗set] g' ∈ ({g} : Oids), Obl.fuel g' 0 μ) ∗ Obl.assigned g 1 ∗
          (γ.γd ↪VAR{.own (1 : Qp).half} g) ∗ isHandoff b γ ℓ }}}
        hl(v(&receive) #b) @ i
      l{{{ (v : Val), RET v; threadExpr i C hl(&v) ∗ £ₒ lc ∗ thKids i ∅ }}} := by
  -- For the internal steps; a task brings its own fuel.
  refine ⟨10, fun lc i b g γ ℓ C => ?_⟩
  iintro %Φ !> ⟨HT, HG, HF, Ag, Gv, #Hh⟩ HΦ
  iloeb as IH generalizing %g
  ihave HF := oblFuels_init _ _ _ $$ HF
  unfold receive
  lwp_step HT HG HF with Hlc : lc +ₕ 1
  icases tlc_split.mp $$ Hlc with ⟨Hlc, Hc1⟩
  lwp_expr_simp
  lwp_bind hl(!#b) HT
  icases oblFuels_add 1 8 _ $$ HF with ⟨HF1, HF⟩
  unfold isHandoff
  ihave Hacc := alwaysI_acc (E := ⊤) (N := Na) (P := handoffInv b γ.γd ℓ)
    (fun _ _ => CoPset.mem_full) $$ Hh
  ihave Hacc := fupd_mupd (Expr := Exp) (State := State) _ _ _ $$ Hacc
  imod Hacc with ⟨Hinv, Hclose⟩
  iapply lwp_credit_later $$ Hc1
  inext
  unfold handoffInv
  icases Hinv with
    ⟨%g₀, (⟨Hb, Gv₀, Kg, #Wg⟩ | ⟨%f, %a, %K, Hb, Gv₀, Htask⟩ | ⟨%f, %a, Hb, Gv₀⟩)⟩
  · -- The cell is empty: renew the inbox, and loop.
    iapply lwp_load (o := 0) (C := _ ++ C) (G := {g}) (R := ∅) $$ [HT HG HF1 Hb]
    · iframe HT Hb
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Hb⟩
    ihave %hg := ghost_var_agree _ _ _ _ _ $$ Gv Gv₀
    subst g₀
    imod Obl.discharge_leaf (⊤ \ ↑Na) (.thread i) {g} g
      (Iris.Std.LawfulSet.mem_singleton.mpr rfl) $$ HG Kg Ag with ⟨HG, -⟩
    imod Obl.new (⊤ \ ↑Na) (.thread i) _ 0 (((3 : Nat) : Measure) + 10) $$ [] HG with
      ⟨%g', -, HG, Kg', Ag', Fg', #Wg'⟩
    · iapply parLe_thread
    imod ghost_var_update_halves g' γ.γd g g $$ Gv Gv₀ with ⟨Gv, Gv₀⟩
    imod Hclose $$ [Hb Gv₀ Kg']
    · inext
      iexists g'
      ileft
      iframe
      iexact Wg'
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    ihave HG := Par.kids_congr (B := {g'}) ?_ $$ HG
    · intro z
      simp
    icases (Obl.fuel_add g' _ _ _).mp $$ Fg' with ⟨F3, F10⟩
    ihave F3 : oblFuels {g'} 3 $$ [F3]
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact F3
    unfold vNone
    lwp_step HT HG F3
    lwp_step HT HG F3
    lwp_expr_simp
    lwp_step HT HG F3
    lwp_expr_simp
    iapply IH $$ %g' HT HG [F10] Ag' Gv HΦ
    iapply BigSepS.bigSepS_singleton.mpr
    iexact F10
  · -- A task: its container moves up to the thread, the inbox is discharged, and the task runs
    -- with the container's fuel.
    unfold handoffTask
    icases Htask with ⟨%c, %ℓt, %μ, %P, Kg, Kc, Ac, Fc, %hlt, HP, #Task⟩
    iapply lwp_load (o := 0) (C := _ ++ C) (G := {g}) (R := ∅) $$ [HT HG HF1 Hb]
    · iframe HT Hb
      iapply stepPre_nil $$ HG HF1
    iintro ⟨HT, ⟨-, HG, -⟩, Hb⟩
    icases ghostVar_combine_halves _ _ _ $$ [Gv Gv₀] with ⟨Gv, %hg⟩
    · iframe
    subst g₀
    imod Obl.move_up (⊤ \ ↑Na) (.thread i) {g} g {c} c (Iris.Std.LawfulSet.mem_singleton.mpr rfl)
      (Iris.Std.LawfulSet.mem_singleton.mpr rfl) $$ HG Kg with ⟨%hcg, HG, Kg⟩
    imod Obl.discharge_leaf (⊤ \ ↑Na) (.thread i) _ g (by simp) $$ HG [Kg] Ag with ⟨HG, -⟩
    · iapply Par.kids_congr _ $$ Kg
      intro z
      simp
    icases (Obl.fuel_add c _ _ _).mp $$ Fc with ⟨Fμ, F10⟩
    imod Hclose $$ [Hb Gv]
    · inext
      iexists g
      iright
      iright
      iexists f, a
      iframe
    imodintro
    ihave HT := (threadExpr_fill i C _ _).mpr $$ HT
    lwp_expr_simp
    ihave HG := Par.kids_congr (B := {c}) ?_ $$ HG
    · intro z
      simp at hcg ⊢
      grind
    ihave F10 : oblFuels {c} 10 $$ [F10]
    · unfold oblFuels
      iapply BigSepS.bigSepS_singleton.mpr
      iexists _
      iexact F10
    unfold vSome
    lwp_step HT HG F10
    lwp_step HT HG F10
    lwp_step HT HG F10
    lwp_expr_simp
    lwp_step HT HG F10
    lwp_step HT HG F10
    lwp_expr_simp
    iapply lwp_mupd
    unfold taskAt
    iapply Task $$ %(0 : Fuel) %i %({c} : Oids) %(Parent.obl c) %K %C [HT HG Fμ Kc HP]
    · iframe HT HG Kc HP
      isplitl [Fμ]
      · iapply BigSepS.bigSepS_singleton.mpr
        iexact Fμ
      · ipureintro
        exact fun _ h => h
    iintro %rv ⟨HT, -, HG, Kc⟩
    imod Obl.discharge_leaf ⊤ (.thread i) {c} c (Iris.Std.LawfulSet.mem_singleton.mpr rfl)
      $$ HG [Kc] Ac with ⟨HG, -⟩
    · iapply Par.kids_congr _ $$ Kc
      intro z
      simp
    imodintro
    iapply HΦ
    iframe HT Hlc
    iapply Par.kids_congr _ $$ HG
    intro z
    simp
  · iexfalso
    iapply ghostVar_half_whole_false $$ [Gv Gv₀]
    iframe

end Specs

/-! ## The handoff cell, at the level of traces -/

section Traces
variable {GF : BundledGFunctors}

/-- The cell `b` holds `v` in the current state of the trace (any fraction). -/
@[lantana_alias tr_cell]
def trCell (b : Loc) (v : Val) : TrProp Exp State :=
  ∃ₜ dq : DFrac, TrProp.state (pointstoSat b dq v)

@[lantana_alias tr_cell_intro]
theorem trCell_intro (b : Loc) (dq : DFrac) (v : Val) :
    TrProp.state (pointstoSat b dq v) ⊆ trCell b v :=
  fun _ h => ⟨dq, h⟩

/-- At all times the cell is empty or holds a task. -/
@[lantana_alias handoff_tr]
def handoffTr (b : Loc) : TrProp Exp State :=
  □ₜ (trCell b vNone ∨ₜ ∃ₜ (f : Val) (a : Val), trCell b (vSome f a))

@[lantana_alias handoff_inv_trSpec_ext]
theorem handoffInvTrSpec_ext (b : Loc) :
    (□ₛ handoffInvTrSpec (GF := GF) b).external ⊆ handoffTr b := by
  intro τ h m hm
  rcases h m hm with ⟨h, _⟩ | ⟨f, a, h, _⟩ | ⟨f, a, h, _⟩
  · exact .inl ⟨.own (1 : Qp).half, h⟩
  · exact .inr ⟨f, a, .own 1, h⟩
  · exact .inr ⟨f, a, .own 1, h⟩

end Traces

end Lantana.Examples.Handoff
