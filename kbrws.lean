import Mathlib
--import Mrdi
import Mrdi.ListToSet



@[reducible]
def f := FreeGroup (Fin 2)

def a : f := FreeGroup.mk [(1, true)]
def b : f := FreeGroup.mk [(2, true)]

def rels_list := [a * b * a⁻¹ * b⁻¹ * a⁻¹, b * a * b⁻¹ * a⁻¹ * b⁻¹]
def rels := List.toSet rels_list

@[reducible]
def g := PresentedGroup rels

def a' : g := PresentedGroup.of 1

theorem to_group_eq_one_of_mem_closure' {G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}
  (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
  ∀ x ∈ Subgroup.normalClosure rels, (FreeGroup.lift f) x = 1 := by
    apply PresentedGroup.to_group_eq_one_of_mem_closure h

theorem x (word : FreeGroup α) (rels : Set (FreeGroup α)) (h : word ∈ rels) :
  (QuotientGroup.mk word : PresentedGroup rels) = 1 := by
    simp only [QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure h

theorem x' (word : FreeGroup α) (rels_list : List (FreeGroup α)) (h : word ∈ rels_list) :
  (QuotientGroup.mk word : PresentedGroup (List.toSet rels_list)) = 1 := by
    simp only [QuotientGroup.eq_one_iff]
    apply Subgroup.subset_normalClosure
    simp only [List.toSet_mem, h]

theorem y {G : Type*} [Group G] {a b : G} (h : a = b) : a * b⁻¹ = 1 := by
  exact mul_inv_eq_one.mpr h

-- better
theorem overlap {a b c d : G} [Group G] (h : a = b) (h' : a * c = b * d) :
  d = c := by
    rw [h] at h'
    apply mul_left_cancel h'.symm

theorem overlap' {a b c d : G} [Group G] (h : a = b) (h' : c * a = d * b) :
  d = c := by
    rw [h] at h'
    apply mul_right_cancel h'.symm

-- TODO get rid of exponents
theorem g_triv : ∀ x : g, x = 1 := by
  -- set _g1 : g := .of 1 with _g1_def
  -- set _g2 : g := (.of 1)⁻¹ with _g2_def
  -- set _g3 : g := .of 2 with _g3_def
  -- set _g4 : g := (.of 2)⁻¹ with _g4_def
  set _g1 : f := .of 1 with _g1_def
  set _g2 : f := (.of 1)⁻¹ with _g2_def
  set _g3 : f := .of 2 with _g3_def
  set _g4 : f := (.of 2)⁻¹ with _g4_def

  -- relations
  have h1 : (QuotientGroup.mk (_g1*_g2) : g) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_one, QuotientGroup.mk_div, QuotientGroup.mk_pow, QuotientGroup.mk_zpow]
    apply mul_inv_self
  have h2:
    a⁻¹*a = 1 := by apply inv_mul_self
  have h3:
    _g3*_g4 = 1 := sorry
  have h4:
    _g4*_g3 = 1 := sorry
  have h5:
    -- a * b * a⁻¹ * b⁻¹ * a⁻¹
    (QuotientGroup.mk (_g2*_g4*_g1) : g) = (QuotientGroup.mk (_g1*_g4) : g) := by
      rw [← mul_inv_eq_one]
      suffices h : (QuotientGroup.mk rels_list[0] : PresentedGroup rels) = 1
      · simp [← h, a, b, _g2_def, _g1_def, _g4_def, PresentedGroup.of, FreeGroup.of, rels_list]
        group
        sorry
      apply x'
      apply List.get_mem
  have h6:
    _g4*_g2*_g3 = _g3*_g2 := sorry

  -- start rws
  have h7 : --5, 1:
    (QuotientGroup.mk (_g1*_g4*_g2) : g) = (QuotientGroup.mk (_g2*_g4) : g)  := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_one,
        QuotientGroup.mk_div, QuotientGroup.mk_pow, QuotientGroup.mk_zpow]
      solve
      | apply overlap' h1
        simp only [one_mul, mul_one, sq, ← mul_assoc,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_one,
          QuotientGroup.mk_div, QuotientGroup.mk_pow, QuotientGroup.mk_zpow]
        repeat congr 1
      | apply overlap h5
        simp only [one_mul, mul_one, sq, ← mul_assoc,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_one,
          QuotientGroup.mk_div, QuotientGroup.mk_pow, QuotientGroup.mk_zpow]
        repeat congr 1


  have h8 : --1, 5:
    _g1^2*_g4 = _g4*_g1 := by
      symm
      apply overlap h1
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
  rewrite
  sorry
