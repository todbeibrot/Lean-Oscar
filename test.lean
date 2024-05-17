import Mrdi
import Mathlib
import Std


open Mrdi Lean Lean.Elab Command Term Lean.Elab.Tactic

#start_server
#start_server

#echo (5 : ℕ)
#echo (6 : Int)

def test_int : Int := by load_file "int"
#readMrdi Int from "int"
#eval test_int
#echo test_int


def x₂ : FreeGroup (Fin 4) := by load_file "free_group_word"
#readMrdi FreeGroup (Fin 4) from "free_group_word"
#print x₂
-- #writeMrdi x₂ to "test"
-- def x₃ : FreeGroup (Fin 2) := by load_file "test"

-- theorem test1 : x₂ = x₃ := by rfl
--#eval x₂ doesn't work cause `Repr FreeGroup` is not implemented
--#echo x₂


def l : List (Fin 10) := by load_file "array"
#readMrdi List (Fin 10) from "array"
#eval l
#echo l


def p : Equiv.Perm (Fin 5) := c[2, 3, 1]
--#writeMrdi p to "lean_perm"
--def p2 : Equiv.Perm (Fin 5) := by load_file "lean_perm"
--#readMrdi Equiv.Perm (Fin 5) from "lean_perm"
--#eval p
--#eval p2
--#echo p doesn't work cause p and p2 are not def equal. They still evaluate to the same value.


#readMrdi Array ℕ from "array"

#readMrdi Int from "int"

def A' : Matrix (Fin 3) (Fin 3) ℚ := !![3, 0, 4; 5, 10, 6; 1, 2, 3]
#writeMrdi A' to "Matrix"
def B : Matrix (Fin 3) (Fin 3) ℚ := by load_file "Matrix"
--#echo A doesn't work cause A and B are not def equal. They still evaluate to the same value.
#eval A'
#eval B


def A : Matrix (Fin 3) (Fin 3) ℚ := !![3, 0, 4; 5, 10, 6; 1, 2, 3]
def A_inv : Matrix (Fin 3) (Fin 3) ℚ := by matrix_inverse A
theorem test3 : A * A_inv = 1 := by
  simp[A, A_inv]
  ext i j
  fin_cases i
  all_goals fin_cases j
  any_goals norm_num [_root_.mkRat, Rat.normalize]
  any_goals rfl


#eval A_inv
#print A_inv
#eval A * A_inv

def i : ℤ := by load_file "int"

#print i

theorem x' : i = 42 := by
  rfl

#echo i
#echo (42 : ℕ )
--#echo A

#print test_int


def d  : Equiv.Perm (Fin 5) := c[1, 2, 3, 4]
def b0 : Equiv.Perm (Fin 5) := c[2, 1, 3]
def b1 : Equiv.Perm (Fin 5) := c[1, 3, 4]
def b2 : Equiv.Perm (Fin 5) := c[3, 2, 4]
def b3 : Equiv.Perm (Fin 5) := c[3, 1, 4]
def b4 : Equiv.Perm (Fin 5) := c[1, 2]

theorem test2 : d ∈ Group.closure {b0, b1, b2, b3, b4} := by
  perm_group_membership

def tuple₁ : ℕ × Bool × ℤ × ℚ := ⟨1, true, 42, 1/3⟩
def tuple₂ : ℕ × Bool × ℤ × ℚ := by load_file "tuple"

#eval tuple₂

@[reducible]
def f := FreeGroup (Fin 2)

def a : f := FreeGroup.mk [(1, true)]
def b : f := FreeGroup.mk [(2, true)]

def rels_list := [a * b * a⁻¹ * b⁻¹ * a⁻¹, b * a * b⁻¹ * a⁻¹ * b⁻¹]
@[reducible]
def rels := List.toSet rels_list

namespace kbmag

@[reducible]
def f := FreeGroup (Fin 2)

@[reducible]
def a : f := FreeGroup.mk [(0, true)]
@[reducible]
def b : f := FreeGroup.mk [(1, true)]

@[reducible]
def rels_list := [a⁻¹ * b⁻¹ * a * b * a⁻¹, b⁻¹ * a⁻¹ * b * a * b⁻¹]
@[reducible]
def rels := List.toSet rels_list

@[reducible]
def g := PresentedGroup rels

set_option maxRecDepth 10000000000000000000000
set_option maxHeartbeats 1000000000000000000000

def g_triv : ∀ (x : g), x = 1 := by
  kbmag (1 : g)

end kbmag
