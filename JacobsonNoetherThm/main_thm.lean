import JacobsonNoetherThm.AlgebraInstance
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Subring

open Classical

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

theorem aux0 [CharP D p] :
  ∀ a : D, a ∉ k → ∃ m ≥ 1, a ^ (p ^ m) ∈ k := sorry

def δ (a : D) : D → D := fun x ↦ a * x - x * a

theorem finial_aux [CharP D p] (a : D) (a_nin_k : a ∉ k) :
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ ^ n) a = 0 := by
  -- letI : CharP k p := inferInstance
  obtain ⟨m, hm⟩ := aux0 a a_nin_k (p := p)
  use m
  constructor
  · exact hm.1
  · intro n hn
    let f (a : D) : D → D := fun x ↦ a * x
    let g (a : D) : D → D := fun x ↦ x * a
    have delta : δ a = f a - g a := rfl
    have inter1 : (f a) ∘ (g a) = (g a) ∘ (f a) := by
      funext x
      dsimp [f, g]; exact Eq.symm (mul_assoc a x a)
    have inter2 : (δ ^ (p ^ m)) a = ((f ^ (p ^ m)) a) - ((g ^ (p ^ m)) a) := by
      funext x
      -- #check sub_pow_char_pow D (a * x)
      sorry
    sorry



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
  have : ∃ a : D, a ∉ k := by exact choose_element_in_complementary_set h
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
  have a_not_commute : ∃ b : D , δ b ≠ 0 := by
    by_contra nh
    push_neg at nh
    have : ∀ x : D, (δ a) x = a * x - x * a := fun x ↦ rfl
    have : a ∈ k := by
      have : ∀ x : D, a* x = x * a :=sorry
      refine Subring.mem_carrier.mp ?_
      unfold Subring.center
      dsimp
      refine Semigroup.mem_center_iff.mpr ?_
      exact fun g ↦ Eq.symm (SemiconjBy.eq (this g))
    sorry



  have : ∃ n ≥ 1,∃ b : D , (δ a) ^[n] b ≠ 0 ∧ (δ a) ^[n + 1] b = 0 := by

    --yy

    sorry

  obtain ⟨n, hn, b, hb⟩ := this
  let c := (δ a) ^[n] b
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
    have ccc : c = (δ a) ^[n] b := rfl
    rw [ccc]
    have ttt : δ a ((δ a)^[n] b) = (δ a)^[n + 1] b := Eq.symm (Function.iterate_succ_apply' (δ a) n b)
    rw [ttt, hb.right]


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
