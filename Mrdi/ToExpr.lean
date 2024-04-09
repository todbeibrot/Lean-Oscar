import Mathlib

/- This file should contain diverse `ToExpr` instances -/

open Qq
open Lean hiding Rat mkRat

section DebuggingTools

open Meta Lean.Elab Command Term
-- for debugging
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

-- for debugging
elab "#myreduce " val:term : command =>
  liftTermElabM do
    let valE ← Term.elabTerm val none
    let valE ← reduce valE
    logInfo valE

end DebuggingTools

section Rat

instance : ToExpr ℚ where
  toTypeExpr := mkConst ``Rat
  toExpr q := match q with
    | ⟨num, den, _, _⟩ =>
        mkApp2 (mkConst ``mkRat) (toExpr num) (toExpr den)

end Rat

-- section Cycle

-- open List

-- #check Quotient.rep

-- instance [ToExpr α] : ToExpr (Cycle α) where
--   toTypeExpr := mkApp (mkConst ``Cycle) (toTypeExpr α)
--   toExpr s := sorry

-- def test1 [DecidableEq α] [Fintype α] [LinearOrder α] (s : Cycle α) : List α := by
--   let x : Quotient (IsRotated.setoid α) := s
--   --let y := Quotient.rep x

--   sorry

-- end Cycle

section Permutations

open Equiv Equiv.Perm

-- -- TODO should we panic instead of using default?
-- def Cycle.formPerm' [DecidableEq α] (s : Cycle α) : Perm α :=
--   if h : s.Nodup then Cycle.formPerm s h else default

-- -- TODO should we panic instead of using default?
-- instance [Fintype α] [LinearOrder α] [DecidableEq α] [ToExpr α] : ToExpr (Equiv.Perm α) where
--   toTypeExpr := mkApp (mkConst ``Equiv.Perm) (toTypeExpr α)
--   toExpr p :=
--     let ⟨l, h_lprod, h_isCycle, h_pairwiseDisjoint⟩ := cycleFactors p
--     let l2 := l.map (fun p => if h : p ∈ l then toCycle p (h_isCycle p h) else default)
--     let l3 := l2.map Cycle.formPerm'
--     let new_p := l3.prod
--     sorry

-- def test (p : Perm (Fin (n + 1))) : List (List (Fin (n + 1))) :=
--   Id.run <| do
--     let ⟨cycles, _⟩ := cycleFactors p
--     let mut l : List (List (Fin (n + 1))) := []
--     for cycle in cycles do
--       for i in List.range (n + 1) do
--         if cycle.toFun i ≠ i then
--           let aux : List (Fin (n + 1)) := cycle.toList i
--           l := aux :: l
--           break
--     return l

instance : ToExpr (Equiv.Perm (Fin (n + 1))) where
  toTypeExpr := mkApp (mkConst ``Equiv.Perm) (toTypeExpr (Fin n))
  toExpr p := Id.run <| do
    let ⟨cycles, _⟩ := cycleFactors p
    let mut l : List (List (Fin (n + 1))) := []
    for cycle in cycles do
      for i in List.range (n + 1) do
        if cycle.toFun i ≠ i then
          let aux : List (Fin (n + 1)) := cycle.toList i
          l := aux :: l
          break
    return q((List.map List.formPerm $l).prod)

end Permutations
