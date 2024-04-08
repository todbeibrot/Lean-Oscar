import Mathlib
import Mrdi.mrdi
import Mrdi.randomstuff
import Mrdi.fromMrdi
import Mrdi.toMrdi
import Mrdi.stream
import Mrdi.ToExpr
import Std
import Mrdi.server
import Qq
import Mathlib.Tactic.ToExpr



namespace Mrdi

open Qq Lean Elab Tactic Meta IO.MrdiFile Expr

syntax "load_file " term : tactic
elab_rules : tactic
  | `(tactic| load_file $file) => do
    let fileE ← elabTerm file q(String)
    let goal ← getMainGoal
    goal.withContext do
      let α ← goal.getType
      let a ← IO.MrdiFile.load_mrdi_from_file α fileE (trace := False)
      goal.assign a




section Matrix_inverse

-- Takes a matrix, returns the type of the elements and the dimensions
private def matrix_type (u) (x : Q(Type $u)) : MetaM (Q(Type u) × Q(ℕ) × Q(ℕ)) := match x with
  | ~q(((Matrix (Fin ($m + 1)) (Fin ($n + 1)))) $α) => return (q($α), q($m) ,q($n))
  | _ => throwError "input didn't match expected type"

def matrix_inverse' (A : Expr) (goal : MVarId) : TacticM Unit := do
  let A_mrdi : Mrdi ← Mrdi? A
  let inv_mrdi ← julia "matrix inverse" A_mrdi
  let A'' : Except String (Matrix (Fin 3) (Fin 3) ℚ) := fromMrdi? inv_mrdi
  let A''' ← Lean.ofExcept A''
  let AE := toExpr A'''
  goal.assign AE
  return

def matrix_inverse'' (A : Expr) (goal : MVarId) : TacticM Unit := do
  let tA ← inferType A
  let .sort u ← instantiateMVars (← whnf (← inferType tA)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr tA}"
  let (α, m, n) ← matrix_type ql(v) tA
  let A_mrdi : Mrdi ← Mrdi? A
  let inv_mrdi ← julia "matrix inverse" A_mrdi
  let inv : Q(Matrix (Fin ($m + 1)) (Fin ($n + 1)) $α) ← eval_mrdi q(Matrix (Fin ($m + 1)) (Fin ($n + 1)) $α) inv_mrdi
  let _ ← synthInstanceQ q(ToExpr (Matrix (Fin ($m + 1)) (Fin ($n + 1)) $α))
  let x := q(toExpr $inv)
  let e ← unsafe evalExpr Expr q(Expr) x
  goal.assign e
  return

def matrix_inverse (A : Expr) (goal : MVarId) : TacticM Unit := do
  let tA ← inferType A
  let .sort u ← instantiateMVars (← whnf (← inferType tA)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr tA}"
  let (α, m, n) ← matrix_type ql(v) tA
  let e ← julia' "matrix inverse" A q(Matrix (Fin ($m + 1)) (Fin ($n + 1)) $α)
  goal.assign e
  return

syntax "matrix_inverse " term : tactic
elab_rules : tactic
  | `(tactic| matrix_inverse $A) => do
    let A ← elabTerm A none
    let goal ← getMainGoal
    matrix_inverse A goal

def A : Matrix (Fin 3) (Fin 3) ℚ := !![3, 0, 4; 5, 10, 6; 1, 2, 3]
-- def A_inv : Matrix (Fin 3) (Fin 3) ℚ := by matrix_inverse A
-- #eval A_inv
-- #print A_inv
-- #eval A * A_inv

end Matrix_inverse



section test_nat

def test_nat (A : Expr) (goal : MVarId) : TacticM Unit := do
  let tA ← inferType A
  let .sort u ← instantiateMVars (← whnf (← inferType tA)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr tA}"
  let A_mrdi : Mrdi ← Mrdi? A
  let A' : Except String Nat := fromMrdi? A_mrdi
  let A'' ← ofExcept A'
  let AE := toExpr A''
  let e := toExpr ((← ofExcept (fromMrdi? A_mrdi)) : ℕ)
  goal.assign AE
  return

syntax "test_nat " term : tactic
elab_rules : tactic
  | `(tactic| test_nat $A) => do
    let A ← elabTerm A none
    let goal ← getMainGoal
    test_nat A goal

def x : ℕ := by
  test_nat 12

#print x

end test_nat



section Permutation

-- like `Lean.Expr.app4?`
-- TODO how can we use Q instead?
@[inline] def app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

-- TODO better names
private partial def Set.toList {u} {G : Q(Type u)} (S : Q(Set $G)) : MetaM Q(List $G) := do
  match S with
    | ~q(Set.singleton $a) =>
        return q([$a])
    | ~q(Set.insert $a $s) => do
        let as : Q(List $G) ← toList q($s)
        return q(($a) :: $as)
    | ~q(Insert.insert $a $s) => do
        let as : Q(List $G) ← toList q($s)
        return q(($a) :: $as)
    | ~q(Singleton.singleton $a) =>
        return q([$a])
    | e => do
        try
          let some (_, _, _, a, s) := app5? e ``Insert.insert | throwError "not an insert"
          let a : Q($G) := a
          let s : Q(Set $G) := s
          let as : Q(List $G) ← toList q($s)
          return q($a :: $as)
        catch _ => do
          let some (_, _, _, a) := app4? e ``Singleton.singleton | throwError s!"not a singleton: {e}"
          let a : Q($G) := a
          return q([$a])

def PermsToList (u) (α : Q(Type $u)) (g : Q($α)) (gens : Q(Set $α)) : MetaM $ Q(List $α) := do
  let gens : Q(List $α) ← Set.toList gens
  return q($g :: $gens)

def permutation (goal : MVarId) : TacticM Unit := do
  goal.withContext do
    let goal_type ← goal.getType
    let some (g_type, _, _, g, closure_set) := app5? goal_type ``Membership.mem | throwError "not a goal of type g ∈ G"
    let .sort sort_u ← inferType g_type | throwError "not a sort"
    let some α := app1? g_type ``Equiv.Perm | throwError "not an Equiv"
    have α : Q(Type) := α
    let f_type := q(FreeGroup $α)
    let some u := sort_u.dec | throwError "not a type{indentExpr (.sort sort_u)}"
    have g_type : Q(Type $u) := g_type
    let some (_, _, gens) :=  closure_set.app3? ``Group.closure | throwError "G is not a Group.closure"
    let g_and_perms ← PermsToList u g_type g gens

    let _ ← unsafe evalExpr (List (Equiv.Perm (Fin 5))) q(List (Equiv.Perm (Fin 5))) g_and_perms

    let x ← julia' "echo" g_and_perms q(List (Equiv.Perm (Fin 5)))
    logInfo x

    --let x ← julia' "permutation" b f_type
    --logInfo x
    return

/- Solves goals of type `x ∈ Group.closure {a, b, c}` where x, a, b, c are permutations -/
syntax "permutation " : tactic
elab_rules : tactic
  | `(tactic| permutation) => do
    let goal ← getMainGoal
    permutation goal

def a : Equiv.Perm (Fin 5) := c[2, 3, 1]
def b1 : Equiv.Perm (Fin 5) := c[1, 2]
def b2 : Equiv.Perm (Fin 5) := c[4, 3]
def b3 : Equiv.Perm (Fin 5) := c[3, 2]
def b4 : Equiv.Perm (Fin 5) := c[3, 1]

theorem test2 : a ∈ Group.closure {b1, b2, b3, b4} := by
  --permutation
  sorry

-- TODO ToExpr (List (Equiv.Perm (Fin 5)))

end Permutation

end Mrdi
