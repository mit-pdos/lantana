/-
Copyright (c) The Lantana-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from Iris-Lean's `Iris.BI.WeakestPre`, whose header reads:
  Copyright (c) The Iris-Lean Contributors
  Released under Apache 2.0 license as described in the file LICENSE.
Modified by the Lantana-Lean Contributors; the module documentation describes the changes.
-/
module

public import Iris.BI
public import Iris.BI.WeakestPre
public import Lantana.Init

/-! # Notations for the liveness weakest precondition

Rocq `lantana/program_logic/lwp_notation.v`, after Iris-Lean's `WP` notations
(`Iris.BI.WeakestPre`): `lWP e @ s; i; E {{ Φ }}` is `Lwp.lwp s i E e Φ` for thread `i`;
without `s`, `NotStuck` (`?{{ Φ }}` for `MaybeStuck`); without `E`, `⊤`. Texan triples
`l{{{ P }}} e @ i; E l{{{ x y, RET v; Q }}}` are `∀ Φ, P -∗ (∀ x y, Q -∗ Φ v) -∗ lWP e @ i; E {{ Φ }}`
(persistent, `□`, inside `iprop`; no `▷`, unlike Iris's).
-/

@[expose] public section

namespace Lantana

open Iris Lean

/-- The liveness weakest precondition, with a stuckness `A` and a thread id `B`. -/
@[lantana_alias Lwp]
class Lwp (PROP Expr : Type _) (Val : outParam (Type _)) (A B : Type _) where
  lwp : A → B → CoPset → Expr → (Val → PROP) → PROP

/-- `e @ s ; i ; E`, `e @ i ; E`, `e @ i`, each optionally followed by `?` (`MaybeStuck`). -/
syntax lwpExpr := term:max " @ " term:max (" ; " term:max)? (" ; " term:max)? (" ?")?

declare_syntax_cat lwpPostcondInner
syntax ident ", " term : lwpPostcondInner
syntax term : lwpPostcondInner

declare_syntax_cat lwpPostcond
syntax "{" noWs "{ " lwpPostcondInner " }" noWs "}" : lwpPostcond

syntax (name := lwp) "lWP " lwpExpr ppSpace lwpPostcond : term

syntax lwpTexanPostcondInner :=
  ((ppSpace (binderIdent <|> bracketedBinder))+ ", ")? " RET " term:min "; " term:min

declare_syntax_cat lwpTexanPostcond
syntax "l{{{ " lwpTexanPostcondInner " }}}" : lwpTexanPostcond
declare_syntax_cat lwpTexanPrecond
syntax "l{{{ " term:min " }}}" : lwpTexanPrecond

syntax (name := lwpTexanTriple) lwpTexanPrecond ppSpace lwpExpr ppSpace lwpTexanPostcond : term

/-- The expression, stuckness, thread id and mask of an `lwpExpr`. -/
meta def parseLwpExpr : TSyntax ``lwpExpr →
    MacroM (TSyntax `term × TSyntax `term × TSyntax `term × TSyntax `term) := fun
  | `(lwpExpr| $e @ $a $[; $b]? $[; $c]? $[?%$q]?) => do
    let stuck ← if q.isSome then `(Stuckness.MaybeStuck) else `(Stuckness.NotStuck)
    match b, c with
    | some i, some E =>
      if q.isSome then Macro.throwError "lWP: `?` cannot be combined with an explicit stuckness"
      return (e, a, i, E)
    | some E, none => return (e, stuck, a, E)
    | none, none => return (e, stuck, a, ←`(⊤))
    | none, some _ => Macro.throwUnsupported
  | _ => Macro.throwUnsupported

meta def parseLwpPostcondInner (stx : TSyntax `lwpPostcondInner) : MacroM (TSyntax `term) := do
  match stx with
  | `(lwpPostcondInner| $v:ident, $Φ:term) => `(fun $v => iprop($Φ))
  | `(lwpPostcondInner| $Φ:term) => return iprop(Φ)
  | _ => Macro.throwUnsupported

@[macro lwp]
meta def lwpMacro : Macro := fun stx => do
  match stx with
  | `(lWP%$tk $expr $postcond) =>
    let (e, s, i, E) ← parseLwpExpr expr
    let `(lwpPostcond| {{ $inner:lwpPostcondInner }}) := postcond | Macro.throwUnsupported
    let Φ ← parseLwpPostcondInner inner
    `($(BI.wrapIpropSpan tk stx ``Lwp.lwp) $s $i $E $e $Φ)
  | _ => Macro.throwUnsupported

private meta def transformTexanBinders
    (xs : Array (TSyntax [`Lean.binderIdent, `Lean.Parser.Term.bracketedBinder])) :
    MacroM <| TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] :=
  xs.mapM fun
    | `(binderIdent|_) => `(hole|_)
    | `(binderIdent|$i:ident) => `(ident|$i)
    | `(bracketedBinder|$x) => `(bracketedBinder|$x)

meta def parseLwpTexanTriple : Syntax → MacroM Term
  | `(l{{{ $P:term }}} $lwpExpr l{{{ $[$[$xs]* ,]? RET $pat ; $Q:term }}}) => do
    let k ← match xs with
      | some xs =>
        let xs ← transformTexanBinders xs
        `(iprop(∀ $xs*, $Q:term -∗ Φ $pat))
      | none => `($Q:term -∗ Φ $pat)
    `(∀ Φ, $P -∗ $k -∗ (lWP $lwpExpr {{ Φ }}))
  | _ => Macro.throwUnsupported

/-- Inside `iprop`, a texan triple is persistent (`□`). -/
@[macro Iris.BI.iprop]
meta def lwpTexanTripleIprop : Macro
  | `(iprop($P)) => do `(iprop(□ $(← parseLwpTexanTriple P)))
  | _ => Macro.throwUnsupported

/-- As a term, a texan triple is a validity statement. -/
@[macro lwpTexanTriple]
meta def lwpTexanTripleTerm : Macro
  | P => do `(⊢ $(← parseLwpTexanTriple P))

meta def unexpandLwpPostcondInner : TSyntax `term → PrettyPrinter.UnexpandM (TSyntax `lwpPostcondInner)
  | `(fun $v:ident => iprop($Φ:term)) => `(lwpPostcondInner|$v:ident, $Φ:term)
  | `(iprop($Φ:term)) => `(lwpPostcondInner| $Φ:term)
  | `(fun $v:ident => $Φ:term) => `(lwpPostcondInner|$v:ident, $Φ:term)
  | `($Φ:term) => `(lwpPostcondInner| $Φ:term)

meta def makeLwpExpr (s i E e : TSyntax `term) : PrettyPrinter.UnexpandM (TSyntax ``lwpExpr) := do
  match s, E with
  | `(Stuckness.NotStuck), `(⊤) => `(lwpExpr| $e:term @ $i:term)
  | `(Stuckness.NotStuck), E => `(lwpExpr| $e:term @ $i:term ; $E:term)
  | `(Stuckness.MaybeStuck), `(⊤) => `(lwpExpr| $e:term @ $i:term ?)
  | `(Stuckness.MaybeStuck), E => `(lwpExpr| $e:term @ $i:term ; $E:term ?)
  | s, E => `(lwpExpr| $e:term @ $s:term ; $i:term ; $E:term)

@[app_unexpander Lwp.lwp]
meta def unexpanderLwp : PrettyPrinter.Unexpander
  | `($_lwp $s $i $E $e $Φ) => do
    let lwpExpr ← makeLwpExpr s i E e
    let inner ← unexpandLwpPostcondInner Φ
    `(lWP $lwpExpr {{ $inner }})
  | _ => throw ()

end Lantana
