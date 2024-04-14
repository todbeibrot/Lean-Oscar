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

-- def matrix_inverse' (A : Expr) (goal : MVarId) : TacticM Unit := do
--   let A_mrdi : Mrdi ← Mrdi? A
--   let inv_mrdi ← julia "matrix inverse" A_mrdi
--   let A'' : Except String (Matrix (Fin 3) (Fin 3) ℚ) := fromMrdi? inv_mrdi
--   let A''' ← Lean.ofExcept A''
--   let AE := toExpr A'''
--   goal.assign AE
--   return

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

-- TODO how can I use `Lean.Meta.replaceTargetEq` and get `eqProof` as a new goal without writing a new tactic for it?
/--
  Convert the given goal `Ctx |- target` into `Ctx |- targetNew` and an equality proof `eqProof : target = targetNew`.
-/
def replaceTargetEq (mvarId : MVarId) (targetNew : Expr) : MetaM (MVarId × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `replaceTarget
    let target   ← mvarId.getType
    let eq       ← mkEq target targetNew
    let mvarEq   ← mkFreshExprSyntheticOpaqueMVar eq `eqProof
    let tag      ← mvarId.getTag
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let u        ← getLevel target
    let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, mvarEq, mvarNew]
    mvarId.assign val
    return (mvarNew.mvarId!, mvarEq.mvarId!)

-- like `Lean.Expr.app4?`
@[inline] def app5? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 5 then
    some (e.appFn!.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

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

def PermsToList (u) (α : Q(Type $u)) (g : Q($α)) (gens : Q(Set $α)) : MetaM $ Q(List $α) × Q(List $α) := do
  let gens : Q(List $α) ← Set.toList gens
  return (q($g :: $gens), q($gens))

def permutation (goal : MVarId) : TacticM Unit := do
  let goal_type ← goal.getType
  let some (g_type, γ, mem_inst, g, closure_set) := app5? goal_type ``Membership.mem | throwError "not a goal of type g ∈ G"
  let .sort sort_v ← inferType γ | throwError "not a sort"
  let some v := sort_v.dec | throwError "not a type{indentExpr (.sort sort_v)}"
  have γ : Q(Type $v) := γ
  have closure_set : Q($γ) := closure_set
  let .sort sort_u ← inferType g_type | throwError "not a sort"
  let some u := sort_u.dec | throwError "not a type{indentExpr (.sort sort_u)}"
  have g_type : Q(Type $u) := g_type
  have g : Q($g_type) := g
  let some (_, inst, gens) :=  closure_set.app3? ``Group.closure | throwError "G is not a Group.closure"
  have _ : Q(Group $g_type) := inst
  let (g_and_gens, gens) ← PermsToList u g_type g gens
  let n : Q(ℕ) := q(List.length $gens)
  let gens_vector : Q(Vector $g_type $n) := q(⟨$gens, rfl⟩)
  let n' ← unsafe evalExpr ℕ q(ℕ) n
  have n : Q(ℕ) := toExpr n'
  let mrdi : Mrdi ← IO.MrdiFile.Mrdi? g_and_gens
  let word_mrdi : Mrdi ← julia "permutation" mrdi
  let word : Q(FreeGroup (Fin $n)) ← IO.MrdiFile.eval_mrdi q(FreeGroup (Fin $n)) word_mrdi
  let word : Q(Expr) := q(toExpr $word)
  let word ← unsafe evalExpr Expr q(Expr) word
  have word : Q(FreeGroup (Fin (List.length $gens))) := word
  let _ ← synthInstanceQ q(Inhabited $g_type)
  let prod := q(FreeGroup.lift (fun (x : Fin (List.length $gens)) => Vector.get $gens_vector x) $word)
  have _ : Q(Membership $g_type $γ) := mem_inst
  let targetNew := q($prod ∈ $closure_set)
  let (new_goal, eq_goal) ← replaceTargetEq goal targetNew
  let eq_goal ← eq_goal.withContext do
    -- TODO make the code for the tactics cleaner
    let tacticCode ← `(tactic| congr; ext x; fin_cases x; any_goals rfl)
    -- TODO what does the `x` do?
    let (eq_goal, x) ← Elab.runTactic eq_goal tacticCode
    return eq_goal
  let new_goal ← new_goal.withContext do
    let tacticCode ← `(tactic|
      try apply Group.InClosure.inv; try exact Group.InClosure.one; repeat' {
        any_goals apply Group.InClosure.mul
        try any_goals apply Group.InClosure.inv
        try any_goals solve | exact Group.InClosure.one  |
        {
          apply Group.InClosure.basic
          simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, Equiv.symm_swap]
        }
      }
    )
    -- TODO what does the `x` do?
    let (new_goal, x) ← Elab.runTactic new_goal tacticCode
    return new_goal
  replaceMainGoal (new_goal ++ eq_goal)

/- Solves goals of type `x ∈ Group.closure {a, b, c}` where x, a, b, c are permutations -/
syntax "permutation " : tactic
elab_rules : tactic
  | `(tactic| permutation) => do
    let goal ← getMainGoal
    permutation goal


def d : Equiv.Perm (Fin 5) := c[1, 4]
def b1 : Equiv.Perm (Fin 5) := c[1, 2]
def b2 : Equiv.Perm (Fin 5) := c[4, 3]
def b3 : Equiv.Perm (Fin 5) := c[3, 2]
def b4 : Equiv.Perm (Fin 5) := c[3, 1]

theorem test3 [Group α] (v : Vector α n) (i : Fin n) : Vector.get v i ∈ Group.closure {x : α | x ∈ v.val} := by

  sorry

theorem test2 : d ∈ Group.closure {b1, b2, b3, b4} := by
  permutation
  simp

  change b4⁻¹ * b2⁻¹ * b4⁻¹ ∈ Group.closure {b1, b2, b3, b4}

  repeat
    apply Group.InClosure.mul
    try any_goals solve |
      simp only [Group.InClosure.one, Group.InClosure.inv, Group.InClosure.basic, Fin.isValue,
        Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, Equiv.symm_swap, test3]




end Permutation

end Mrdi
