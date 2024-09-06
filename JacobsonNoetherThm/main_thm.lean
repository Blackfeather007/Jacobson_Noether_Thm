import JacobsonNoetherThm.AlgebraInstance
import JacobsonNoetherThm.CharPAux
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.Subring

open Classical

variable (D : Type*) [DivisionRing D] [Algebra.IsAlgebraic (Subring.center D) D]

local notation3 "k" => (Subring.center D)

/-- Jacobson-Noether theorem in the `CharP D 0` case -/
theorem JacobsonNoether_charZero [CharP D 0] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  let _ : CharZero k := (CharP.charP_zero_iff_charZero k).mp (by infer_instance)
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr h
  exact ⟨a, ⟨ha, (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)).separable⟩⟩


/-- Jacobson-Noether theorem in the `CharP D p` case -/
theorem JacobsonNoether_charP {p : ℕ} [Fact p.Prime] [CharP D p] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  by_contra! insep
  have hinsep : ∀ x : D, IsSeparable k x → x ∈ k :=
    fun x h ↦ Classical.byContradiction fun hx ↦ insep x hx h
  -- The element `a` below is in `D` but not in `k`.
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr h
  -- We construct another element `b` that does not commute with `a`.
  obtain ⟨b, hb1⟩ : ∃ b : D , (δ a) b ≠ 0 := by
    rw [Subring.mem_center_iff, not_forall] at ha
    use ha.choose
    show a * ha.choose - ha.choose * a ≠ 0
    simpa only [ne_eq, sub_eq_zero] using Ne.symm ha.choose_spec
  -- We find a maximum natural number `n` such that `(δ a) ^ n ≠ 0`.
  obtain ⟨n, hn, hb⟩ : ∃ n > 0, ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨m, -, hm2⟩ := final_aux p ha hinsep
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      refine ⟨ p ^ m, ⟨pow_pos (Nat.Prime.pos (@Fact.out _ _)) m, ?_ ⟩ ⟩
      simp only [hm2 (p^ m + 1) (by linarith), LinearMap.zero_apply]
    refine ⟨Nat.find exist, ⟨(Nat.find_spec exist).1, ?_, (Nat.find_spec exist).2⟩⟩
    set t := (Nat.find exist - 1 : ℕ) with ht
    by_cases choice : 0 < t
    · have := @Nat.find_min (H := exist) _ t ?_
      · rw [not_and, ht, Nat.sub_add_cancel] at this
        · exact this choice
        · replace choice : 1 ≤ t := Nat.one_le_of_lt choice
          apply le_trans choice
          exact Nat.sub_le (Nat.find exist) 1
      · rw [ht]
        apply Nat.sub_one_lt
        apply ne_of_gt
        exact (Nat.find_spec exist).1
    · rw [not_lt, Nat.le_zero] at choice
      have := Nat.eq_add_of_sub_eq (Nat.find_spec exist).1 ht.symm
      simp only [gt_iff_lt, choice, Nat.succ_eq_add_one, zero_add] at this
      rw [this]
      simp only [Function.iterate_one, ne_eq]
      exact hb1

  let c := ((δ a) ^ n) b
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  have important (n) : δ a (((δ a) ^ n) b) = ((δ a) ^ (n + 1)) b := by
    rw [LinearMap.pow_apply, LinearMap.pow_apply, ← Nat.succ_eq_add_one]
    exact Eq.symm (Function.iterate_succ_apply' (δ a) n b)
  have hc : c * a = a * c := by
    rw [← show (f a) c = a * c by rfl, ← show (g a) c = c * a by rfl]
    suffices (f a - g a) c = 0 from by
      rw [sub_eq_add_neg] at this
      rw [← zero_add (g a c), add_eq_of_eq_add_neg]
      exact this.symm
    rw [← show (δ a) c = (f a - g a) c by rfl, show c = ((δ a) ^ n) b by rfl, important, hb.right]

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


theorem Jacobson_Noether (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases @CharP.char_is_prime_or_zero D _ _ _ p _ with h1 | h2
  · apply JacobsonNoether_charP _ h hp
  -- · exact @JacobsonNoether_charP D _ p ⟨h1⟩ _ _ h
  exact @JacobsonNoether_charZero D _ (CharP.congr p h2) _ h
