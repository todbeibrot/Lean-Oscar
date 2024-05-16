import Mathlib
import Mrdi.RBNode

/-
This file contains diverse `ToExpr` instances.
Note that the resulting expressions are not necessarily definitionally equal to their origin.
-/

open Qq
open Lean hiding Rat mkRat

section DebuggingTools

open Meta Lean.Elab Command Term

elab "#testToExpr " val:term : command =>
  liftTermElabM do
    let valE ← Term.elabTerm val none
    let t : Q(Type) ← inferType valE
    let valE : Q($t) := valE
    let _ ← synthInstanceQ q(ToExpr $t)
    let e := q(toExpr $valE)
    let valE ← instantiateMVars valE
    let e ← instantiateMVars e
    let e ← unsafe evalExpr Expr q(Expr) e
    if ← isDefEq e valE then
      logInfo "is def eq"
    else
      let e ← whnf e
      let valE ← whnf valE
      if ← isDefEq e valE then
        logInfo "is def eq with whnf"
      else
        let e ← reduce e
        let valE ← reduce valE
        if ← isDefEq e valE then
          logInfo "is def eq with reduce"
        else
          logInfo s!"is not definitionally equal: \n\n e: {e} \n\n valE: {valE}"

elab "#myreduce " val:term : command =>
  liftTermElabM do
    let valE ← Term.elabTerm val none
    let valE ← reduce valE
    logInfo valE

end DebuggingTools

deriving instance ToExpr for JsonNumber
deriving instance ToExpr for Json

section Rat

instance : ToExpr ℚ where
  toTypeExpr := mkConst ``Rat
  toExpr q := match q with
    | ⟨num, den, _, _⟩ =>
        mkApp2 (mkConst ``mkRat) (toExpr num) (toExpr den)

end Rat

section Permutations

open Equiv Equiv.Perm

-- TODO mkConst in toTypeExpr need specified List of Levels?
instance : ToExpr (Equiv.Perm (Fin (n + 1))) where
  toTypeExpr := mkApp (mkConst ``Equiv.Perm) (toTypeExpr (Fin n))
  toExpr p := Id.run <| do
    let ⟨cycles, _⟩ := Equiv.Perm.cycleFactors p
    let mut l : List (List (Fin (n + 1))) := []
    for cycle in cycles do
      for i in List.range (n + 1) do
        if cycle.toFun i ≠ i then
          let aux : List (Fin (n + 1)) := p.toList i
          l := aux :: l
          break
    have n' : Q(ℕ) := toExpr n
    have l' : Q(List (List (Fin ($n' + 1)))) := toExpr l
    return q((List.map List.formPerm $l').prod)

end Permutations

section FreeGroup

instance {α : Type u}  [ToExpr α] [DecidableEq α] [ToLevel.{u}] : ToExpr $ FreeGroup α where
  toTypeExpr := mkApp (mkConst ``FreeGroup [toLevel.{u}]) (toTypeExpr α)
  toExpr g :=
    have eα : Q(Type $(toLevel.{u})) := toTypeExpr α
    let wordE : Q(List ($eα × Bool)) := toExpr g.toWord
    q(FreeGroup.mk $wordE)

end FreeGroup
