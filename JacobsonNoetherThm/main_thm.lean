import JacobsonNoetherThm.AlgebraInstance
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable


theorem aux1 {R : Type*} [DivisionRing R] [CharP R 0] [Algebra.IsAlgebraic (Subring.center R) R] :
    ∃ x : R, x ∉ (Subring.center R) ∧ IsSeparable (Subring.center R) x :=
  sorry


theorem aux2 {R : Type*} [DivisionRing R] {p : ℕ} [Fact p.Prime] [CharP R p] [Algebra.IsAlgebraic (Subring.center R) R] :
    ∃ x : R, x ∉ (Subring.center R) ∧ IsSeparable (Subring.center R) x :=
  sorry



theorem Jacobson_Noether {R : Type*} [DivisionRing R] {p : ℕ} [CharP R p] [Algebra.IsAlgebraic (Subring.center R) R] :
    ∃ x : R, x ∉ (Subring.center R) ∧ IsSeparable (Subring.center R) x := by
  rcases @CharP.char_is_prime_or_zero R _ _ _ p _ with h1 | h2
  · exact @aux2 R _ p ⟨h1⟩ _ _
  exact @aux1 R _ (CharP.congr p h2) _
