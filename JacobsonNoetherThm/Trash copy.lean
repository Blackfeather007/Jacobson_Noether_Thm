import Mathlib

variable {R : Type*} [DivisionRing R]

instance : Algebra (Subring.center R) R := by
  refine Algebra.ofModule ?h₁ ?h₂
  · intro r x y
    exact smul_mul_assoc r x y
  · intro r x y
    exact mul_smul_comm r x y

instance : Field (Subring.center R) := by
  exact Subring.instField

example [Algebra.IsAlgebraic (Subring.center R) R] : CharZero (Subring.center R) → IsSeparable (Subring.center R) R := by
  intro h
  refine isSeparable_iff.mpr ?_
  intro x
  constructor
  · exact Algebra.IsIntegral.isIntegral x
  · apply PerfectField.separable_of_irreducible
    refine minpoly.irreducible ?right.a.hx
    exact Algebra.IsIntegral.isIntegral x
