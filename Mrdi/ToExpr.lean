import Mathlib

/- This file should contain diverse `ToExpr` instances -/


open Qq


#check Lean.ToExpr
#check Rat.mk'

#reduce Rat.mk' (2 : ℤ) (3 : ℕ)

#check Rat.mul
#check Rat.ofInt

def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right (Int.natAbs num) }

#check mkRat

/- Rat.mul { num := Int.ofNat 2, den := 1, den_nz := Rat.ofInt.proof_1, reduced := ⋯ }
  (Rat.inv { num := Int.ofNat 3, den := 1, den_nz := Rat.ofInt.proof_1, reduced := ⋯ }) -/

instance : Lean.ToExpr ℚ where
  toTypeExpr := Lean.mkConst ``Rat
  toExpr q := match q with
    | ⟨num, den, _, _⟩ =>
        --let numE : Q(ℤ) := Lean.toExpr num
        --let denE : Q(ℕ) := Lean.toExpr den
        --let qE : Q(ℚ) := q(Rat.mk' $numE $denE)
        Lean.mkApp2 (Lean.mkConst ``mkRat) (Lean.toExpr num) (Lean.toExpr den)

#reduce Lean.toExpr (2 : ℚ)

open Lean Meta Lean.Elab Command Term

-- for debugging
elab "#testToExpr " val:term : command =>
  liftTermElabM do
    let valE ← Lean.Elab.Term.elabTerm val none
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
    let valE ← Lean.Elab.Term.elabTerm val none
    let valE ← reduce valE
    logInfo valE

#myreduce ((2 : ℤ) / (3 : ℕ) : ℚ )
#eval ((2 : ℤ) / (3 : ℕ) : ℚ )


#testToExpr ((2 : ℤ) / (3 : ℕ) : ℚ )
