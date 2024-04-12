import Mathlib
import Mrdi.mrdi
import Mrdi.randomstuff
import Mrdi.fromMrdi
import Mrdi.toMrdi
import Mrdi.stream
--import Mrdi.ToExpr
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


def PermsToList (u) (α : Q(Type $u)) (g : Q($α)) (gens : Q(Set $α)) : MetaM $ Q(List $α) := do
  let gens : Q(List $α) ← Set.toList gens
  return q($g :: $gens)

-- def f {β : Type*} [Inhabited β] [Group β] (l : List β) (word : FreeGroup (Fin n)) : β :=
--   (FreeGroup.lift (l[· + 1]!)) word

def permutation (goal : MVarId) : TacticM Unit := do
  let goal_type ← goal.getType
  let some (g_type, γ, mem_inst, g, closure_set) := app5? goal_type ``Membership.mem | throwError "not a goal of type g ∈ G"
  let .sort sort_v ← inferType γ | throwError "not a sort"
  let some v := sort_v.dec | throwError "not a type{indentExpr (.sort sort_v)}"
  have γ : Q(Type $v) := γ
  have closure_set : Q($γ) := closure_set
  let .sort sort_u ← inferType g_type | throwError "not a sort"
  --let some α := app1? g_type ``Equiv.Perm | throwError "not an Equiv"
  --have α : Q(Type) := α
  let some u := sort_u.dec | throwError "not a type{indentExpr (.sort sort_u)}"
  have g_type : Q(Type $u) := g_type
  have g : Q($g_type) := g
  let some (_, inst, gens) :=  closure_set.app3? ``Group.closure | throwError "G is not a Group.closure"
  have _ : Q(Group $g_type) := inst
  let g_and_perms ← PermsToList u g_type g gens
  let n : Q(ℕ) := q(List.length $g_and_perms - 1)
  --let n : Q(ℕ) := q(List.length $g_and_perms)
  let n' ← unsafe evalExpr ℕ q(ℕ) n
  have n : Q(ℕ) := toExpr n'
  let mrdi : Mrdi ← IO.MrdiFile.Mrdi? g_and_perms
  let word_mrdi : Mrdi ← julia "permutation" mrdi
  let word : Q(FreeGroup (Fin $n)) ← IO.MrdiFile.eval_mrdi q(FreeGroup (Fin $n)) word_mrdi
  --let word_test ← unsafe evalExpr (FreeGroup $ Fin n') q(FreeGroup $ Fin $n) word
  --logInfo $ format $ word_test.toWord
  --logInfo $ format $ g_and_perms
  let _ ← synthInstanceQ q(ToExpr $g_type)
  let _ ← synthInstanceQ q(Inhabited $g_type)
  -- TODO why do we need inverse here?
  let prod := q(toExpr ((FreeGroup.lift ($g_and_perms[· + 1]!)) $word)⁻¹)
  let prod : Q($g_type) ← unsafe evalExpr Expr q(Expr) prod
  have _ : Q(Membership $g_type $γ) := mem_inst
  let targetNew := q($prod ∈ $closure_set)
  let (new_goal, eq_goal) ← replaceTargetEq goal targetNew
  replaceMainGoal [new_goal, eq_goal]
  return

/- Solves goals of type `x ∈ Group.closure {a, b, c}` where x, a, b, c are permutations -/
syntax "permutation " : tactic
elab_rules : tactic
  | `(tactic| permutation) => do
    let goal ← getMainGoal
    permutation goal

def a : Equiv.Perm (Fin 5) := c[1, 4]
def b1 : Equiv.Perm (Fin 5) := c[1, 2]
def b2 : Equiv.Perm (Fin 5) := c[4, 3]
def b3 : Equiv.Perm (Fin 5) := c[3, 2]
def b4 : Equiv.Perm (Fin 5) := c[3, 1]

theorem test2 : a ∈ Group.closure {b1, b2, b3, b4} := by
  permutation

  · simp [b1, b2, b3, b4, Equiv.swap_comm]
    repeat any_goals apply Group.InClosure.mul
    any_goals apply Group.InClosure.basic
    any_goals simp
  · congr
    simp [a, Equiv.swap_comm]
    ext x
    fin_cases x
    any_goals simp [Equiv.swap_apply_of_ne_of_ne]

-- TODO ToExpr FreeGroup


end Permutation

end Mrdi
