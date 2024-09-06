import JacobsonNoetherThm.AlgebraInstance
import JacobsonNoetherThm.CharPAux
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.Subring

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

lemma choose_element_in_complementary_set (h : k ≠ (⊤ : Subring D)) : ∃ a : D, a ∉ k := by
  by_contra! nt
  apply h
  rwa [← (Subring.eq_top_iff' (Subring.center D)).symm]

/-- J-N thm for `CharP D 0` case -/
theorem thm_char_zero [CharP D 0] [Algebra.IsAlgebraic k D] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  letI : CharZero k := (CharP.charP_zero_iff_charZero k).mp (by infer_instance)
  obtain ⟨a, ha⟩ := choose_element_in_complementary_set h
  exact ⟨a, ⟨ha, Irreducible.separable (minpoly.irreducible (Algebra.IsIntegral.isIntegral a))⟩⟩

/-- J-N thm for `CharP D p` case -/
theorem thm_char_p {p : ℕ} [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  by_contra! insep
  obtain ⟨a, ha⟩ := choose_element_in_complementary_set h
  have hinsep : ∀ x : D, IsSeparable k x → x ∈ k :=
    fun x h ↦ Classical.byContradiction fun hx ↦ insep x hx h

  have a_not_commute : ∃ b : D , (δ a) b ≠ 0 := by
    by_contra! nh
    apply ha
    apply Subring.mem_center_iff.mpr
    intro x
    have := @eq_add_of_sub_eq' _ _ (a * x) (x * a) 0 (nh x)
    rw [add_zero] at this
    exact this.symm

  have : ∃ n > 0, ∃ b : D , ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨b, hb1⟩ := a_not_commute
    rcases (final_aux p ha hinsep) with ⟨m, _ , hm2⟩
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      use p ^ m
      constructor
      · exact Fin.size_pos'
      · have : (δ a) ^ (p ^ m + 1) = 0 := by
          apply hm2 _
          linarith
        rw [this]; rfl
    classical
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
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  have important (n): δ a (((δ a) ^ n) b) = ((δ a) ^ (n + 1)) b := by
    rw [LinearMap.pow_apply, LinearMap.pow_apply, ← Nat.succ_eq_add_one]
    exact Eq.symm (Function.iterate_succ_apply' (δ a) n b)
  have hc : c * a = a * c := by
    have f_def : (f a) c = a * c := rfl
    have g_def : (g a) c = c * a := rfl
    have prop_d : (δ a) c = (f a - g a) c := rfl
    have prop_c : c = ((δ a) ^ n) b := rfl
    rw [← f_def, ← g_def]
    suffices (f a - g a) c = 0 from by
      rw [sub_eq_add_neg] at this
      rw [← zero_add (g a c), add_eq_of_eq_add_neg]
      exact this.symm
    rw [← prop_d, prop_c, important, hb.right]

  /-
  **The "Ring Tactic" must be use on a CommRing, there is no efficient Tactic if on none CommRing**
  **And the progress is a piece of SHIT**
  **I use so many "rw" Tactic similar to the beginning learning of Lean**
  -/
  let d := c⁻¹ * a * (δ a) ^[n-1] b
  /-
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · ) at hc
    rw [← mul_assoc, inv_mul_cancel₀, one_mul, ← mul_assoc] at hc
    apply_fun (· * c⁻¹) at hc
    rw [mul_assoc, mul_inv_cancel₀, mul_one] at hc
    exact hc.symm
    exact Ne.symm (NeZero.ne' c)
  -/
  have hc': c⁻¹ * a = a * c⁻¹ := by
    calc
      _ = c⁻¹ * a * (c * c⁻¹) := by simp only [mul_inv_cancel_of_invertible, mul_one]
      _ = c⁻¹ * (a * c) * c⁻¹ := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hc]
      _ = (c⁻¹ * c) * a * c⁻¹ := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = _ := by simp only [inv_mul_cancel_of_invertible, one_mul]
  have d_def : d = c⁻¹ * a * (δ a) ^[n-1] b := rfl
  have c_def : c = ((δ a) ^ n) b := rfl
  have c_eq : a * (δ a) ^[n - 1] b - (δ a) ^[n - 1] b * a = c := by
    rw [c_def]
    have : (δ a) ^[n - 1] b = ((δ a) ^ (n - 1)) b :=
      Eq.symm (LinearMap.pow_apply (δ a) (n - 1) b)
    rw [this]
    have : (n - 1) + 1 = n := by exact Nat.sub_add_cancel hn
    rw [← this]
    have : (δ a ^ (n - 1 + 1)) b = (δ a) ((δ a ^ (n - 1)) b) := by rw [important]
    rw [this]
    rfl
  have eq1 : c⁻¹ * a * (δ a)^[n - 1] b - c⁻¹ * (δ a)^[n - 1] b * a = 1 := by
    calc
      _ = c⁻¹ * (a * (δ a)^[n - 1] b) - c⁻¹ * ((δ a)^[n - 1] b * a) := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = c⁻¹ * (a * (δ a)^[n - 1] b - (δ a)^[n - 1] b * a) := Eq.symm (mul_sub_left_distrib c⁻¹ _ _)
      _ = c⁻¹ * c := by rw [c_eq]
      _ = _ := by simp only [inv_mul_cancel_of_invertible]

  have deq : a * d - d * a = a := by
    calc
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * a * (δ a)^[n - 1] b) * a := by rw [d_def]
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * c⁻¹ * (δ a)^[n - 1] b * a := by rw [hc']
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * (c⁻¹ * (δ a)^[n - 1] b * a) := by simp_rw [@NonUnitalRing.mul_assoc]
      _ = a * ((c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * (δ a)^[n - 1] b * a)) := Eq.symm (mul_sub_left_distrib a _ _)
      _ = _ := by
        rw [eq1]
        simp only [mul_one]
  have a_inv : a⁻¹ * a = 1 := by
    refine inv_mul_cancel₀ ?h
    by_contra nh
    rw [nh] at ha
    have : 0 ∈ Subring.center D := Subring.zero_mem (Subring.center D)
    contradiction
  have : 1 + a⁻¹ * d * a = d := by
    calc
      _ = (a⁻¹ * a) + a⁻¹ * d * a := by simp only [add_left_inj, a_inv]
      _ = a⁻¹ * a + a⁻¹ * (d * a) := by
        simp only [add_right_inj]
        rw [@NonUnitalRing.mul_assoc]
      _ = a⁻¹ * (a + d * a) := by rw [@left_distrib]
      _ = a⁻¹ * (a * d - d * a + d * a) := by rw [deq]
      _ = a⁻¹ * (a * d) := by simp only [sub_add_cancel]
      _ = (a⁻¹ * a) * d := by rw [@NonUnitalRing.mul_assoc]
      _ = _ := by simp only [a_inv, one_mul]
  obtain ⟨r, hr⟩ := (l1 p d hinsep)

  have a_inv : a⁻¹ * a = 1 := by
    apply inv_mul_cancel₀ _
    by_contra nh
    rw [nh] at ha
    have : 0 ∈ Subring.center D := Subring.zero_mem (Subring.center D)
    contradiction
  have inv_a : a * a⁻¹ = 1 := by
    apply mul_inv_cancel₀ _
    by_contra nh
    rw [nh] at ha
    have : 0 ∈ Subring.center D := Subring.zero_mem (Subring.center D)
    contradiction

  have eq : d ^ (p ^ r) = 1 + d ^ (p ^ r) := by
    calc
      _ = (1 + a⁻¹ * d * a) ^ (p ^ r) := by rw [this]
      _ = 1 ^ (p ^ r) + (a⁻¹ * d * a) ^ (p ^ r) := by
        rw [add_pow_char_pow_of_commute]
        exact Commute.one_left (a⁻¹ * d * a)
      _ = 1 + a⁻¹ * d ^ (p ^ r) * a := by
        simp only [one_pow, add_right_inj]
        have (s : ℕ): a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s := by
          induction' s with s ih
          · simp only [pow_zero, mul_one, a_inv]
          · symm
            calc
              _ = (a⁻¹ * d * a) ^ s * (a⁻¹ * d * a) := by
                rw [@npow_add]
                simp only [pow_one]
              _ = a⁻¹ * d ^ s * (a * a⁻¹) * d * a := by simp_rw [← ih, @NonUnitalRing.mul_assoc]
              _ = a⁻¹ * d ^ s * d * a := by simp only [inv_a, mul_one]
              _ = a⁻¹ * (d ^ s * d) * a := by simp_rw [@NonUnitalRing.mul_assoc]
              _ = _ := by
                simp only [mul_eq_mul_right_iff, mul_eq_mul_left_iff, inv_eq_zero, or_self_right]
                left
                exact Eq.symm (pow_succ d s)
        exact Eq.symm (CancelDenoms.derive_trans rfl (this (p ^ r)))
      _ = _ := by
        simp only [add_right_inj]
        have : a * d ^ p ^ r = d ^ p ^ r * a := by exact Eq.symm (hr.comm a)
        calc
          _ = a⁻¹ * (d ^ p ^ r * a) := by simp_rw [@NonUnitalRing.mul_assoc]
          _ = a⁻¹ * (a * d ^ p ^ r) := by rw [this]
          _ = (a⁻¹ * a) * d ^ p ^ r := by simp_rw [@NonUnitalRing.mul_assoc]
          _ = _ := by simp only [a_inv, one_mul]
  simp only [self_eq_add_left, one_ne_zero] at eq


theorem Jacobson_Noether [Algebra.IsAlgebraic k D] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · exact @thm_char_p D _ p ⟨h1⟩ _ _ h
  exact @thm_char_zero D _ (CharP.congr p h2) _ h
