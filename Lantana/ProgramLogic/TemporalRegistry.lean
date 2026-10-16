/-
Copyright (c) The Lantana-Lean Contributors
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Iris.Instances.Lib.SavedProp
public import Lantana.ProgramLogic.HistoryInterp

/-! # The temporal registry

Rocq `lantana/program_logic/temporal_registry.v`: an append-only list of the trace-visible
structures (`alwaysI`, `untilI`), each tagged with its registration position (a history
index), and of a marker per check of the adequacy. Positions are non-decreasing, so a record
about position `n` can tell whether an item was registered before the check at `n` (then the
check certified it) or during step `n`. The list is Iris-Lean's `MonoList` ghost state. The
registry also saves trace predicates (`savedTrI`), which identify the step-indexed reading of
a content's canonical trace property across the registry.

The registry state `regStateWith Hd` holds the list and, for each entry, a history event at
its position and its interpretation `Hd` (given by the temporal layer). The program logic
threads this state, so registering an entry (`regRegister`) is a plain ghost update.
-/

@[expose] public noncomputable section

namespace Lantana

open Iris Iris.BI Iris.ProofMode

/-! ## Entries -/

/-- An entry of the registry: a marker (one per check of the adequacy), a registered
`alwaysI` (its namespace and saved trace predicate) or a registered `untilI` (its namespace,
its obligation and the saved trace predicates of its two sides). -/
@[lantana_alias reg_entry]
inductive RegEntry where
  | mark
  | always (N : Namespace) (γ : GName)
  | until (N : Namespace) (k : Oid) (γP γQ : GName)
  deriving DecidableEq, Inhabited

attribute [lantana_alias RMark] RegEntry.mark
attribute [lantana_alias RAlways] RegEntry.always
attribute [lantana_alias RUntil] RegEntry.until

/-- Entries form a discrete OFE with Leibniz equality (Rocq `leibnizO reg_entry`). -/
instance : COFE RegEntry := COFE.ofDiscrete _

instance : OFE.Discrete RegEntry := ⟨id⟩

/-- The registry is well formed: positions are non-decreasing along the list. -/
@[lantana_alias reg_wf]
def regWf (l : List (Nat × RegEntry)) : Prop :=
  ∀ (i j : Nat) (pi pj : Nat × RegEntry), i ≤ j → l[i]? = some pi → l[j]? = some pj →
    pi.1 ≤ pj.1

@[lantana_alias reg_wf_nil]
theorem regWf_nil : regWf [] := by
  intro _ _ _ _ _ hi
  simp at hi

@[lantana_alias reg_wf_app]
theorem regWf_append {l : List (Nat × RegEntry)} {p : Nat} {e : RegEntry} (hwf : regWf l)
    (hle : ∀ pe ∈ l, pe.1 ≤ p) : regWf (l ++ [(p, e)]) := by
  intro i j pi pj hij hi hj
  by_cases hjl : j < l.length
  · rw [List.getElem?_append_left hjl] at hj
    rw [List.getElem?_append_left (Nat.lt_of_le_of_lt hij hjl)] at hi
    exact hwf i j pi pj hij hi hj
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hjl), List.getElem?_singleton] at hj
    split at hj
    · cases hj
      by_cases hil : i < l.length
      · rw [List.getElem?_append_left hil] at hi
        exact hle _ (List.mem_of_getElem? hi)
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hil), List.getElem?_singleton] at hi
        split at hi
        · cases hi
          exact Nat.le_refl _
        · cases hi
    · cases hj

@[lantana_alias reg_wf_lookup_pos]
theorem regWf_lookup_pos {l : List (Nat × RegEntry)} {i j : Nat} {pi pj : Nat × RegEntry}
    (hwf : regWf l) (hij : i ≤ j) (hi : l[i]? = some pi) (hj : l[j]? = some pj) :
    pi.1 ≤ pj.1 :=
  hwf i j pi pj hij hi hj

/-! ## Ghost state -/

/-- The ghost state of the registry that a world provides: a monotone list of entries and
saved trace predicates. The language is an output parameter (D30): a world carries one
language. -/
@[lantana_alias tregGpreS] -- Rocq `tregGS.tregGpreS`
class RegGpreS (Expr : outParam Type) (State : outParam Type) (GF : BundledGFunctors) where
  [listG : MonoListG GF (Nat × RegEntry)]
  [predG : SavedPredG GF (Trace Expr State)]

attribute [reducible, instance] RegGpreS.listG RegGpreS.predG

/-- The ghost state of the registry: the world's ghost state and the ghost name of the list. -/
@[lantana_alias tregGS] -- Rocq `tregGS.tregGS`
class RegGS (Expr : outParam Type) (State : outParam Type) (GF : BundledGFunctors)
    extends RegGpreS Expr State GF where
  /-- The ghost name of the registry list. -/
  regName : GName

attribute [lantana_alias treg_inG] RegGS.toRegGpreS
attribute [lantana_alias treg_name] RegGS.regName

#lantana_ignore «tregΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#lantana_ignore «subG_tregΣ» "Subsumed by BundledGFunctors typeclass synthesis"

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [RegGS Expr State GF]

open MonoList

/-- The authoritative registry list. -/
@[lantana_alias reg_auth]
def regAuth (l : List (Nat × RegEntry)) : IProp GF :=
  iprop(⌜regWf l⌝ ∗ (RegGS.regName (GF := GF) ↪●ML l))

/-- A persistent snapshot: the registry list has the prefix `l`. -/
@[lantana_alias reg_lb]
def regLb (l : List (Nat × RegEntry)) : IProp GF :=
  iprop(⌜regWf l⌝ ∗ (RegGS.regName (GF := GF) ↪◯ML l))

/-- A persistent snapshot: the `j`-th entry of the registry is `e`, registered at
position `p`. -/
@[lantana_alias reg_idx]
def regIdx (j p : Nat) (e : RegEntry) : IProp GF :=
  iprop(∃ l : List (Nat × RegEntry),
    ⌜l[j]? = some (p, e) ∧ regWf l⌝ ∗ (RegGS.regName (GF := GF) ↪◯ML l))

@[lantana_alias reg_lb_persistent]
instance regLb_persistent (l : List (Nat × RegEntry)) : Persistent (regLb (GF := GF) l) := by
  unfold regLb; infer_instance

@[lantana_alias reg_idx_persistent]
instance regIdx_persistent (j p : Nat) (e : RegEntry) : Persistent (regIdx (GF := GF) j p e) := by
  unfold regIdx; infer_instance

@[lantana_alias reg_auth_timeless]
instance regAuth_timeless (l : List (Nat × RegEntry)) : Timeless (regAuth (GF := GF) l) := by
  unfold regAuth; infer_instance

@[lantana_alias reg_lb_timeless]
instance regLb_timeless (l : List (Nat × RegEntry)) : Timeless (regLb (GF := GF) l) := by
  unfold regLb; infer_instance

@[lantana_alias reg_idx_timeless]
instance regIdx_timeless (j p : Nat) (e : RegEntry) : Timeless (regIdx (GF := GF) j p e) := by
  unfold regIdx; infer_instance

@[lantana_alias reg_auth_wf]
theorem regAuth_wf (l : List (Nat × RegEntry)) : regAuth (GF := GF) l ⊢ ⌜regWf l⌝ := by
  unfold regAuth
  iintro ⟨%hwf, -⟩
  ipureintro
  exact hwf

@[lantana_alias reg_lb_wf]
theorem regLb_wf (l : List (Nat × RegEntry)) : regLb (GF := GF) l ⊢ ⌜regWf l⌝ := by
  unfold regLb
  iintro ⟨%hwf, -⟩
  ipureintro
  exact hwf

@[lantana_alias reg_auth_lb]
theorem regAuth_lb (l : List (Nat × RegEntry)) : regAuth (GF := GF) l ⊢ regLb l := by
  unfold regAuth regLb
  iintro ⟨%hwf, H⟩
  isplitr
  · ipureintro
    exact hwf
  · iapply lb_own_get $$ H

@[lantana_alias reg_lb_idx]
theorem regLb_idx {l : List (Nat × RegEntry)} {j p : Nat} {e : RegEntry}
    (h : l[j]? = some (p, e)) : regLb (GF := GF) l ⊢ regIdx j p e := by
  unfold regLb regIdx
  iintro ⟨%hwf, H⟩
  iexists l
  iframe H
  ipureintro
  exact ⟨h, hwf⟩

#lantana_ignore reg_lb_lb_valid "Local; Iris-Lean's `MonoList.lb_own_valid`"
#lantana_ignore reg_auth_lb_valid "Local; Iris-Lean's `MonoList.auth_lb_own_valid`"

@[lantana_alias reg_auth_idx_lookup]
theorem regAuth_idx_lookup (l : List (Nat × RegEntry)) (j p : Nat) (e : RegEntry) :
    regAuth (GF := GF) l ⊢ regIdx j p e -∗ ⌜l[j]? = some (p, e)⌝ := by
  unfold regAuth regIdx
  iintro ⟨-, Ha⟩ ⟨%l', %⟨hl', -⟩, Hl⟩
  icases auth_lb_own_valid _ _ _ _ $$ Ha Hl with %⟨-, hpre⟩
  ipureintro
  exact prefix_getElem? hpre hl'

@[lantana_alias reg_auth_lb_prefix]
theorem regAuth_lb_prefix (l l' : List (Nat × RegEntry)) :
    regAuth (GF := GF) l ⊢ regLb l' -∗ ⌜l' <+: l⌝ := by
  unfold regAuth regLb
  iintro ⟨-, Ha⟩ ⟨-, Hl⟩
  icases auth_lb_own_valid _ _ _ _ $$ Ha Hl with %⟨-, hpre⟩
  ipureintro
  exact hpre

@[lantana_alias reg_idx_agree]
theorem regIdx_agree (j p p' : Nat) (e e' : RegEntry) :
    regIdx (GF := GF) j p e ⊢ regIdx j p' e' -∗ ⌜p = p' ∧ e = e'⌝ := by
  unfold regIdx
  iintro ⟨%l, %⟨hl, -⟩, H⟩ ⟨%l', %⟨hl', -⟩, H'⟩
  icases lb_own_valid _ _ _ $$ H H' with %hpre
  ipureintro
  have heq : some (p, e) = some (p', e') := by
    rcases hpre with hpre | hpre
    · rw [← hl', prefix_getElem? hpre hl]
    · rw [← hl, prefix_getElem? hpre hl']
  cases heq
  exact ⟨rfl, rfl⟩

/-- The pure part of the marker argument. -/
theorem regWf_prefix_mark {l l' : List (Nat × RegEntry)} {j p m : Nat} {e : RegEntry}
    (hlast : l.getLast? = some (m, .mark)) (hpre : l <+: l') (hwf' : regWf l')
    (hl' : l'[j]? = some (p, e)) : l[j]? = some (p, e) ∨ m ≤ p := by
  by_cases hj : j < l.length
  · left
    obtain ⟨x, hx⟩ : ∃ x, l[j]? = some x := ⟨l[j], List.getElem?_eq_getElem hj⟩
    rw [hx, ← hl', prefix_getElem? hpre hx]
  · right
    have hlen : l.length - 1 < l.length := by
      cases l with
      | nil => cases hlast
      | cons _ _ => simp
    rw [List.getLast?_eq_getElem?] at hlast
    exact hwf' _ j _ _ (by omega) (prefix_getElem? hpre hlast) hl'

/-- The marker argument: an entry is either in the prefix that ends with the marker of
position `m`, or it was registered at a position at least `m`. -/
@[lantana_alias reg_idx_lb_pos]
theorem regIdx_lb_pos {l : List (Nat × RegEntry)} {m : Nat} (j p : Nat) (e : RegEntry)
    (hlast : l.getLast? = some (m, .mark)) :
    regLb (GF := GF) l ⊢ regIdx j p e -∗ ⌜l[j]? = some (p, e) ∨ m ≤ p⌝ := by
  unfold regLb regIdx
  iintro ⟨-, Hl⟩ ⟨%l', %⟨hl', hwf'⟩, Hl'⟩
  icases lb_own_valid _ _ _ $$ Hl Hl' with %hpre
  ipureintro
  rcases hpre with hpre | hpre
  · exact regWf_prefix_mark hlast hpre hwf' hl'
  · exact .inl (prefix_getElem? hpre hl')

@[lantana_alias reg_auth_append]
theorem regAuth_append (l : List (Nat × RegEntry)) (p : Nat) (e : RegEntry)
    (hle : ∀ pe ∈ l, pe.1 ≤ p) :
    regAuth (GF := GF) l ⊢ |==> (regAuth (l ++ [(p, e)]) ∗ regIdx l.length p e) := by
  unfold regAuth regIdx
  iintro ⟨%hwf, Ha⟩
  have hwf' := regWf_append (e := e) hwf hle
  imod auth_own_update_app _ [(p, e)] $$ Ha with ⟨Ha, #Hl⟩
  imodintro
  isplitl [Ha]
  · iframe Ha
    ipureintro
    exact hwf'
  · iexists l ++ [(p, e)]
    iframe Hl
    ipureintro
    exact ⟨by simp, hwf'⟩

end

/-- The ghost state of the registry at the name `γ` of the list, over the world's cameras
(D32: the name is small enough for the existential property of satisfiability, unlike
`RegGS Expr State GF`). -/
@[reducible] def RegGS.ofName {Expr State : Type} {GF : BundledGFunctors}
    [RegGpreS Expr State GF] (γ : GName) : RegGS Expr State GF where
  regName := γ

/-- Allocating the registry with an empty list, at the name `γ` (D32). -/
theorem regGS_alloc_names {Expr State : Type} {GF : BundledGFunctors} [RegGpreS Expr State GF] :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      letI := RegGS.ofName (Expr := Expr) (State := State) (GF := GF) γ; regAuth [] := by
  imod MonoList.own_alloc ([] : List (Nat × RegEntry)) with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  unfold regAuth
  iframe Ha
  ipureintro
  exact regWf_nil

/-- Allocating the registry with an empty list. -/
@[lantana_alias reg_alloc]
theorem regGS_alloc {Expr State : Type} {GF : BundledGFunctors} [RegGpreS Expr State GF] :
    ⊢@{IProp GF} |==> ∃ _ : RegGS Expr State GF, regAuth [] := by
  imod regGS_alloc_names (Expr := Expr) (State := State) (GF := GF) with ⟨%γ, H⟩
  imodintro
  iexists RegGS.ofName γ
  iexact H

/-! ## Saved trace predicates

Saved trace predicates identify the step-indexed reading of a content's canonical trace
property across the registry. -/

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [RegGpreS Expr State GF]

/-- The ghost name `γ` saves the trace predicate `f` (persistently). -/
@[lantana_alias saved_trI]
def savedTrI (γ : GName) (f : Trace Expr State → IProp GF) : IProp GF :=
  saved_pred_own γ .discard f

@[lantana_alias saved_trI_persistent]
instance savedTrI_persistent (γ : GName) (f : Trace Expr State → IProp GF) :
    Persistent (savedTrI γ f) := by
  unfold savedTrI; infer_instance

@[lantana_alias saved_trI_alloc]
theorem savedTrI_alloc (f : Trace Expr State → IProp GF) :
    ⊢@{IProp GF} |==> ∃ γ, savedTrI γ f :=
  saved_pred_alloc f .discard DFrac.valid_discard

/-- Agreement up to a later, which the step-indexed readings absorb. -/
@[lantana_alias saved_trI_agree_fun]
theorem savedTrI_agree_fun (γ : GName) (f g : Trace Expr State → IProp GF) :
    savedTrI γ f ⊢ savedTrI γ g -∗ ▷ (f ≡ g) := by
  refine wand_intro ?_
  refine .trans ?_ (later_mono (discreteFun_equivI f g).mpr)
  refine .trans ?_ later_forall.mpr
  exact forall_intro fun τ => saved_pred_agree γ _ _ f g τ

end

/-! ## The registry state

The list, and for each entry a history event at its position and its interpretation `Hd`
(given by the temporal layer). The program logic threads this state, so registering is a
plain ghost update. -/

/-- Each entry of `l` has a history event at its position and its interpretation `Hd`. The
registry's ghost state (unused here) determines the language, an output parameter, so that
`regEntries Hd l` needs no language annotations. -/
@[lantana_alias reg_entries]
def regEntries {Expr State : Type} {GF : BundledGFunctors} [RegGS Expr State GF]
    [HistGS Expr State GF] (Hd : RegEntry → IProp GF) (l : List (Nat × RegEntry)) : IProp GF :=
  iprop([∗list] pe ∈ l, (∃ st : HistEntry Expr State, histEvent pe.1 st) ∗ Hd pe.2)

section
variable {Expr : Type} {State : Type} {GF : BundledGFunctors} [RegGS Expr State GF]
  [HistGS Expr State GF]

/-- The registry state: the authoritative list and its entries. -/
@[lantana_alias reg_state_with]
def regStateWith (Hd : RegEntry → IProp GF) : IProp GF :=
  iprop(∃ l, regAuth l ∗ regEntries Hd l)

@[lantana_alias reg_state_with_init]
theorem regStateWith_init (Hd : RegEntry → IProp GF) :
    regAuth (GF := GF) [] ⊢ regStateWith Hd := by
  unfold regStateWith regEntries
  iintro Ha
  iexists []
  iframe Ha
  iapply BigSepL.bigSepL_nil.mpr
  iempintro

variable [StateInterp Expr State GF]

/-- The entries of the registry were registered at positions up to the current one. -/
@[lantana_alias reg_entries_bound]
theorem regEntries_bound (Hd : RegEntry → IProp GF) (l : List (Nat × RegEntry))
    (h : List (HistEntry Expr State)) (n : Nat) (σ : State) (tp : ThreadPool Expr) :
    regEntries Hd l ⊢ historyInterp (GF := GF) h n σ tp -∗ ⌜∀ pe ∈ l, pe.1 ≤ n⌝ := by
  have key : ∀ (i : Nat) (pe : Nat × RegEntry), l[i]? = some pe →
      regEntries Hd l ∗ historyInterp (GF := GF) h n σ tp ⊢ ⌜pe.1 ≤ n⌝ := by
    intro i pe hi
    unfold regEntries
    iintro ⟨Hl, HI⟩
    ihave %⟨hlen, -⟩ := historyInterp_wf h n σ tp $$ HI
    icases BigSepL.bigSepL_lookup hi $$ Hl with ⟨⟨%st, He⟩, -⟩
    icases historyInterp_histEvent_lookup h n σ tp pe.1 st $$ [HI He] with %hst
    · iframe
    ipureintro
    have := (List.getElem?_eq_some_iff.mp hst).1
    omega
  refine wand_intro (.trans ?_ pure_forall.mpr)
  refine forall_intro fun pe => ?_
  by_cases hpe : pe ∈ l
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpe
    exact (key i pe hi).trans (pure_mono fun h _ => h)
  · exact pure_intro fun h => absurd h hpe

/-- Registering the entry `e` at the current position `n`, given its interpretation. -/
@[lantana_alias reg_register]
theorem regRegister (Hd : RegEntry → IProp GF) (e : RegEntry) (h : List (HistEntry Expr State))
    (n : Nat) (σ : State) (tp : ThreadPool Expr) :
    regStateWith Hd ⊢ (∀ st : HistEntry Expr State, histEvent n st -∗ Hd e) -∗
      historyInterp h n σ tp ==∗
      historyInterp h n σ tp ∗ regStateWith Hd ∗ ∃ j, regIdx j n e := by
  unfold regStateWith
  iintro ⟨%l, Ha, Hl⟩ He HI
  ihave %hb := regEntries_bound Hd l h n σ tp $$ Hl HI
  ihave #Hnow := historyInterp_histEvent_now h n σ tp $$ HI
  imod regAuth_append l n e hb $$ Ha with ⟨Ha, #Hj⟩
  imodintro
  iframe HI
  isplitl [Ha Hl He]
  · iexists l ++ [(n, e)]
    iframe Ha
    unfold regEntries
    iapply BigSepL.bigSepL_snoc.mpr
    iframe Hl
    isplitr
    · iexists (σ, tp)
      iexact Hnow
    · iapply He $$ Hnow
  · iexists l.length
    iexact Hj

end

end Lantana
