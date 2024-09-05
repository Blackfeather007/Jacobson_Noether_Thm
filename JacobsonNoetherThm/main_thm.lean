import JacobsonNoetherThm.AlgebraInstance
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Subring

-- set_option diagnostics true

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)


theorem aux1 [CharP D 0] [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  letI : CharZero k := (CharP.charP_zero_iff_charZero k).mp (by infer_instance)
  have : ∃ a : D, a ∉ k := by
    by_contra nt
    push_neg at nt
    have : k ≥ (⊤ : Subring D) := fun ⦃x⦄ a ↦ nt x
    have : k ≤ (⊤ : Subring D) := fun ⦃x⦄ a ↦ trivial
    have : k = (⊤ : Subring D) := (Subring.eq_top_iff' (Subring.center D)).mpr nt
    rw [this] at h
    contradiction
  obtain ⟨a, ha⟩ := this
  use a
  constructor
  · exact ha
  · have : Polynomial.Separable (minpoly k a) := by
      apply Irreducible.separable
      apply minpoly.irreducible
      exact Algebra.IsIntegral.isIntegral a
    exact this




theorem aux2 {p : ℕ} [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x :=
  sorry


theorem Jacobson_Noether [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · exact @aux2 D _ p ⟨h1⟩ _ _ h
  exact @aux1 D _ (CharP.congr p h2) _ h
