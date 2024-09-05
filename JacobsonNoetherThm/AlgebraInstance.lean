import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.Algebraic
-- import Mathlib.FieldTheory.Separable

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

instance : Algebra k D := by
  refine Algebra.ofModule ?h₁ ?h₂
  · intro r x y
    exact smul_mul_assoc r x y
  · intro r x y
    exact mul_smul_comm r x y

instance : Field k := Subring.instField
