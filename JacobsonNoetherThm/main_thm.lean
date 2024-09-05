import JacobsonNoetherThm.AlgebraInstance
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

theorem aux1 [CharP D 0] [Algebra.IsAlgebraic k D] :
    ∃ x : D, x ∉ k ∧ IsSeparable k x :=
  sorry


theorem aux2 {p : ℕ} [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D] :
    ∃ x : D, x ∉ k ∧ IsSeparable k x :=
  sorry



theorem Jacobson_Noether {p : ℕ} [CharP D p] [Algebra.IsAlgebraic k D] :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · exact @aux2 D _ p ⟨h1⟩ _ _
  exact @aux1 D _ (CharP.congr p h2) _
