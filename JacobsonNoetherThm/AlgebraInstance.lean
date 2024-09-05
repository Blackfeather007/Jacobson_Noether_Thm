import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.Algebraic
-- import Mathlib.FieldTheory.Separable

variable {R : Type*} [DivisionRing R]

instance : Algebra (Subring.center R) R := by
  refine Algebra.ofModule ?h₁ ?h₂
  · intro r x y
    exact smul_mul_assoc r x y
  · intro r x y
    exact mul_smul_comm r x y

instance : Field (Subring.center R) := by
  exact Subring.instField
