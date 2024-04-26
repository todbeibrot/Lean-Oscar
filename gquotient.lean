import Mrdi
import Mathlib
import Std

/-
A simpler way of proving that a finitely presented group is not trivial is to exhibit
a finite quotient (rather than a coset table). For this, you just have to find
non-trivial permutations, one per generator, and check that they satisfy the relations.
The GAP command "GQuotients" will return epimorphisms from an f.p. group to a
given (typically, finite) permutation group.
-/


def x (α) [FinEnum α] [Inhabited α]  (rels : List $ FreeGroup α) : FreeGroup α ⧸ Subgroup.normalClosure (List.toSet rels) :=
  1

def word_list : List (FreeGroup (Fin 2)) := [FreeGroup.mk [(0, true), (0, true)], FreeGroup.mk [(1, true), (1, true)],
  FreeGroup.mk [(0, true), (1, true), (0, false), (1, false)]]

def y := x (Fin 2)
  [FreeGroup.mk [(0, true), (0, true)], FreeGroup.mk [(1, true), (1, true)],
  FreeGroup.mk [(0, true), (1, true), (0, false), (1, false)]]

def z : PresentedGroup (List.toSet word_list) := y

--#writeMrdi z to "fpgrouptest"
