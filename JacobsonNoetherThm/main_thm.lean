import JacobsonNoetherThm.AlgebraInstance
import JacobsonNoetherThm.CharPAux
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Subring


variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

theorem JWC_very_cute [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) : ∃ a : D, a ∉ k := by
  by_contra nt
  push_neg at nt
  have : k ≥ (⊤ : Subring D) := fun ⦃x⦄ _ ↦ nt x
  have : k ≤ (⊤ : Subring D) := fun ⦃x⦄ _ ↦ trivial
  have : k = (⊤ : Subring D) := (Subring.eq_top_iff' (Subring.center D)).mpr nt
  rw [this] at h
  contradiction


theorem aux1 [CharP D 0] [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  letI : CharZero k := (CharP.charP_zero_iff_charZero k).mp (by infer_instance)
  have : ∃ a : D, a ∉ k := by exact JWC_very_cute h
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
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  by_contra! insep
  obtain ⟨a, ha⟩ := JWC_very_cute h
  have : ∃ n ≥ 1, ∃ b : D, b ^ n ≠ 0 ∧ b ^ (n + 1) = 0 := by
    --yy
    sorry

  obtain ⟨n, hn, b, hb⟩ := this
  let c := (δ a) ^[n] b
  letI : Invertible c := by sorry
  have hc : c * a = a * c := sorry
  -- j
  let d := c⁻¹ * a * (δ a) ^[n-1] b

  have : ∃ r ≥ 1, d ^ (p ^ r) ∈ k := by sorry -- he
  obtain ⟨r, hr, hd⟩ := this
  --yy
  have eq : d ^ (p ^ r) = 1 + d ^ (p ^ r) := sorry
  sorry


theorem Jacobson_Noether [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · exact @aux2 D _ p ⟨h1⟩ _ _ h
  exact @aux1 D _ (CharP.congr p h2) _ h
