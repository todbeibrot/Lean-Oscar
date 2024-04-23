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
