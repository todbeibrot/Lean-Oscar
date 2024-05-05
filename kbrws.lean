import Mathlib
import Mrdi



@[reducible]
def f := FreeGroup (Fin 2)

def a : f := FreeGroup.mk [(1, true)]
def b : f := FreeGroup.mk [(2, true)]

def rels_list := [a * b * a⁻¹ * b⁻¹ * a⁻¹, b * a * b⁻¹ * a⁻¹ * b⁻¹]
def rels := List.toSet rels_list

@[reducible]
def g := PresentedGroup rels

-- doesnt work well
theorem overlap {a b c d : G} [Group G] (h : a = b) (h' : c = d)
  (h_left : lhs = a * c) (h_right : rhs = b * d) :
  lhs = rhs := by
    rw [h_left, h_right, h, h']

theorem overlap' {a b c d : G} [Group G] (h : a = b) (h' : a * c = b * d) :
  c = d := by
    rw [h] at h'
    apply mul_left_cancel h'

theorem overlap'' {a b c d : G} [Group G] (h : a = b) (h' : c * a = d * b) :
  c = d := by
    rw [h] at h'
    apply mul_right_cancel h'

-- TODO get rid of exponents
theorem g_triv : ∀ x : g, x = 1 := by
  set _g1 := a with _g1_def
  set _g2 := _g1⁻¹ with _g2_def
  set _g3 := b with _g3_def
  set _g4 := _g3⁻¹ with _g4_def

  -- relations
  have h1 : _g1*_g2 = 1 := sorry
  have h2:
    _g2*_g1 = 1 := sorry
  have h3:
    _g3*_g4 = 1 := sorry
  have h4:
    _g4*_g3 = 1 := sorry
  have h5:
    _g2*_g4*_g1 = _g1*_g4 := sorry
  have h6:
    _g4*_g2*_g3 = _g3*_g2 := sorry

  -- start rws
  have h7 : --5, 1:
    _g1*_g4*_g2 = _g2*_g4 := by
      symm
      apply overlap'' h1
      simp only [one_mul, mul_one, sq, ← mul_assoc]
      congr 1
  have h8 : --1, 5:
    _g1^2*_g4 = _g4*_g1 := by
      symm
      apply overlap' h1
      simp only [one_mul, mul_one, sq, mul_assoc]
      congr 1
  have h9 : --6, 3:
    _g3*_g2*_g4 = _g4*_g2 := by
      symm
      apply overlap'' h3
      simp only [one_mul, mul_one, sq, ← mul_assoc]
      congr 1
  have h10 : --3, 6:
    _g3^2*_g2 = _g2*_g3 := sorry
  have h11 : --2, 7:
    _g2^2*_g4 = _g4*_g2 := sorry
  have h12 : --8, 4:
    _g4*_g1*_g3 = _g1^2 := sorry
  have h13 : --4, 9:
    _g4^2*_g2 = _g2*_g4 := sorry
  have h14 : --10, 2:
    _g2*_g3*_g1 = _g3^2 := sorry
  have h15 : --11, 4:
    _g3 = _g2 := sorry
  have h16 : --3, 12:
    _g1 = 1  := sorry
  -- if something is 1, simplify everywhere
  simp only [h16,     one_mul, mul_one, inv_one] at *
  -- same for inverse
  -- simp only [_g2_def, one_mul, mul_one, inv_one] at *
  have h17 : --13, 2:
    _g4 = _g2 := sorry
  have h18 : --3, 13:
    _g2 = 1 := by
      rw [← h3]
      simp only [sq] at *

      sorry

  sorry
