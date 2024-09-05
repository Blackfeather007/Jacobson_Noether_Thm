import JacobsonNoetherThm.AlgebraInstance
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Subring

open Classical

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

lemma aux0 [CharP D p] :
  ∀ a : D, a ∉ k → ∃ m ≥ 1, a ^ (p ^ m) ∈ k := sorry

def f (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ a * x
  map_add' := fun x y ↦ LeftDistribClass.left_distrib a x y
  map_smul' := by
    intro m x
    simp only [Algebra.mul_smul_comm, RingHom.id_apply]
}

def g (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ x * a
  map_add' := fun x y ↦ RightDistribClass.right_distrib x y a
  map_smul' := by
    intro m x
    simp only [Algebra.smul_mul_assoc, RingHom.id_apply]
}

def δ (a : D) : D →ₗ[k] D := {
  toFun := f a - g a
  map_add' := by
    intro x y
    simp only [Pi.sub_apply, map_add, add_sub_add_comm]
  map_smul' := by
    intro m x
    simp only [Pi.sub_apply, map_smul, RingHom.id_apply, smul_sub]
}

lemma final_aux [CharP D p] (a : D) (a_nin_k : a ∉ k) :
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := sorry

theorem choose_element_in_complementary_set [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) : ∃ a : D, a ∉ k := by
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
  have : ∃ a : D, a ∉ k := choose_element_in_complementary_set h
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
  obtain ⟨a, ha⟩ := choose_element_in_complementary_set h
  have a_not_commute : ∃ b : D , (δ a) b ≠ 0 := by
    by_contra nh
    push_neg at nh
    have : ∀ x : D, (δ a) x = a * x - x * a := fun x ↦ rfl
    have : a ∈ k := by
      have : ∀ x : D, a * x = x * a := by
        intro x
        have : a * x - x * a = 0 := nh x
        calc
          _ = (a * x - x * a) + x * a := by simp only [sub_add_cancel]
          _ = _ := by simp only [this, zero_add]
      exact Semigroup.mem_center_iff.mpr (fun g ↦ Eq.symm (SemiconjBy.eq (this g)))
    contradiction

  have : ∃ n > 0, ∃ b : D , ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨b, hb1⟩ := a_not_commute
    have : ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := final_aux a ha
    rcases this with ⟨m, hm1, hm2⟩
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      use p ^ m
      constructor
      · exact Fin.size_pos'
      · have : (δ a) ^ (p ^ m + 1) = 0 := by
          apply hm2 _
          linarith
        rw [this]; rfl
    have ⟨hex1, hex2⟩ := (Nat.find_spec exist)
    use Nat.find exist
    simp only [gt_iff_lt, Function.iterate_succ, Function.comp_apply, hex1, ne_eq, true_and]
    use b
    constructor
    · let t := (Nat.find exist - 1 : ℕ)
      have : ¬(t > 0 ∧ ((δ a) ^ (t + 1)) b = 0) :=
        have this : t < Nat.find exist := Nat.sub_one_lt_of_lt hex1
        (Nat.find_min exist) this
      have ht : t + 1 = Nat.find exist := Nat.sub_add_cancel hex1
      push_neg at this
      rw [← ht]
      by_cases choice : t > 0
      · exact this choice
      · have : t = 0 := by linarith
        simp only [this, zero_add, Function.iterate_one, ne_eq]
        exact hb1
    · exact hex2

  obtain ⟨n, hn, b, hb⟩ := this
  let c := ((δ a) ^ n) b
  letI : Invertible c := by
    have cne0 : c ≠ 0 := by
      exact hb.left
    use c⁻¹
    · exact inv_mul_cancel₀ cne0
    · exact mul_inv_cancel₀ cne0
  have hc : c * a = a * c := by
    let f (a : D) : D → D := fun x ↦ a * x
    let g (a : D) : D → D := fun x ↦ x * a
    have fff : (f a) c = a * c := rfl
    have ggg : (g a) c = c * a := rfl
    rw [← fff, ← ggg]
    suffices (f a - g a) c = 0 from by
      simp at this
      rw [sub_eq_add_neg] at this
      rw [← zero_add (g a c)]
      rw [add_eq_of_eq_add_neg]
      exact this.symm
    have ddd : (δ a) c = (f a - g a) c := rfl
    rw [← ddd]
    have ccc : c = ((δ a) ^ n) b := rfl
    rw [ccc]
    have ttt : δ a (((δ a) ^ n) b) = ((δ a) ^ (n + 1)) b := by
      rw [LinearMap.pow_apply, LinearMap.pow_apply, ← Nat.succ_eq_add_one]
      exact Eq.symm (Function.iterate_succ_apply' (δ a) n b)
    rw [ttt, hb.right]
  /-
  **The "Ring Tactic" must be use on a CommRing, there is no efficient Tactic if on none CommRing**
  **And the progress is a piece of SHIT**
  **I use so many "rw" Tactic similar to the beginning learning of Lean**
  -/
  let d := c⁻¹ * a * (δ a) ^[n-1] b
  have hc': c⁻¹ * a = a * c⁻¹ := by
    calc
      _ = c⁻¹ * a * (c * c⁻¹) := by simp only [mul_inv_cancel_of_invertible, mul_one]
      _ = c⁻¹ * (a * c) * c⁻¹ := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hc]
      _ = (c⁻¹ * c) * a * c⁻¹ := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = _ := by simp only [inv_mul_cancel_of_invertible, one_mul]
  have d_def : d = c⁻¹ * a * (δ a) ^[n-1] b := rfl
  have eq1 : c⁻¹ * a * (δ a)^[n - 1] b - c⁻¹ * (δ a)^[n - 1] b * a = 1 := by
    calc
      _ = c⁻¹ * (a * (δ a)^[n - 1] b) - c⁻¹ * ((δ a)^[n - 1] b * a) := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = c * ((a * (δ a)^[n - 1] b - (δ a)^[n - 1] b * a)) := by

        sorry

  have deq : a * d - d * a = a := by
    calc
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * a * (δ a)^[n - 1] b) * a := by rw [d_def]
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * c⁻¹ * (δ a)^[n - 1] b * a := by rw [hc']
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * (c⁻¹ * (δ a)^[n - 1] b * a) := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = a * ((c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * (δ a)^[n - 1] b * a)) := Eq.symm (mul_sub_left_distrib a _ _)
      _ = _ := by
        rw [eq1]
        simp only [mul_one]
  have : ∃ r ≥ 0, d ^ (p ^ r) ∈ k := by

    sorry -- he
  obtain ⟨r, hr, hd⟩ := this
  have eq : d ^ (p ^ r) = 1 + d ^ (p ^ r) := by
    calc
      _ = (1 + a⁻¹ * d * a) ^ (p ^ r) := by

        sorry
      _ = 1 ^ (p ^ r) + (a⁻¹ * d * a) ^ (p ^ r) := by

        sorry
      _ = 1 + a⁻¹ * d ^ (p ^ r) * a := sorry
      _ = _ := sorry
  simp only [self_eq_add_left, one_ne_zero] at eq

theorem Jacobson_Noether [Algebra.IsAlgebraic k D] (h : (⊤ : Subring D) ≠ k) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · exact @aux2 D _ p ⟨h1⟩ _ _ h
  exact @aux1 D _ (CharP.congr p h2) _ h
