import Mrdi.Basic
import Mrdi.FromMrdi
import Mrdi.ToMrdi
import Mrdi.Stream
import Mrdi.Server
import Mrdi.Tactics
import Mathlib
import Std


namespace Mrdi
open Lean Lean.Elab Command Term Lean.Elab.Tactic

#start_server
#start_server

#echo (5 : ℕ)
#echo (6 : Int)

def test_int : Int := by load_file "int"
#readMrdi Int from "int"
#eval test_int
#echo test_int


def x₂ : FreeGroup (Fin 2) := by load_file "free_group_word"
#readMrdi FreeGroup (Fin 2) from "free_group_word"
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
  fin_cases i; fin_cases j
  norm_num
  try repeat sorry

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



def d : Equiv.Perm (Fin 5) := c[1, 2, 3, 4]
def b1 : Equiv.Perm (Fin 5) := c[2, 1]
def b2 : Equiv.Perm (Fin 5) := c[4, 3]
def b3 : Equiv.Perm (Fin 5) := c[3, 2, 4, 1]
def b4 : Equiv.Perm (Fin 5) := c[3, 1, 2]

theorem test2 : d ∈ Group.closure {b1, b2, b3, b4} := by
  permutation


end Mrdi
