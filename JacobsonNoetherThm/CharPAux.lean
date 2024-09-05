import JacobsonNoetherThm.AlgebraInstance
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic
import Mathlib.Algebra.CharP.Subring

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

lemma l1 (p : ℕ) [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D] (a : D)
   (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, g, hg, geqf⟩ := @Polynomial.exists_separable_of_irreducible k _ p _ (minpoly k a)
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)) ((NeZero.ne' p).symm)
  have h1 : (Polynomial.aeval a) ((Polynomial.expand k (p ^ n)) g) = 0 := by
    rw [congrArg (⇑(Polynomial.aeval a)) geqf, minpoly.aeval k a]
  simp only [Polynomial.expand_aeval] at h1
  use n
  apply hinsep (a ^ p ^ n) (Polynomial.Separable.of_dvd hg (minpoly.dvd_iff.mpr h1))

lemma l2 (p : ℕ) [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D] {a : D}
   (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n ≥ 1, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, g, hg, geqf⟩ := @Polynomial.exists_separable_of_irreducible k _ p _ (minpoly k a)
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)) ((NeZero.ne' p).symm)
  by_cases nzero : n = 0
  · rw [nzero, pow_zero, Polynomial.expand_one] at geqf
    rw [geqf] at hg
    tauto
  use n
  have h1 : (Polynomial.aeval a) ((Polynomial.expand k (p ^ n)) g) = 0 := by
    rw [congrArg (⇑(Polynomial.aeval a)) geqf, minpoly.aeval k a]
  simp only [Polynomial.expand_aeval] at h1
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr nzero
  exact hinsep (a ^ p ^ n) (Polynomial.Separable.of_dvd hg (minpoly.dvd_iff.mpr h1))

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

lemma comm_fg (a : D) : Commute (f a) (g a) := by
  rw [commute_iff_eq, LinearMap.mk.injEq, AddHom.mk.injEq]
  funext x
  dsimp [f, g]; exact Eq.symm (mul_assoc a x a)

lemma aux1 (a : D) : δ a = f a - g a := rfl

lemma f_pow (a : D) (n : ℕ) : ∀ x : D, ((f a) ^ n).1 x = (a ^ n) * x := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n
  · simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  · simp only [Function.iterate_succ', Function.comp_apply, *]
    rename_i n h
    rw [pow_succ', mul_assoc]; rfl

lemma g_pow (a : D) (n : ℕ) : ∀ x : D, ((g a) ^ n).1 x = x * (a ^ n) := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n
  · simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
  · simp only [Function.iterate_succ', Function.comp_apply, *]
    rename_i n h
    show (x * a ^ n) * a = x * a ^ (n + 1)
    rw [pow_add, pow_one, mul_assoc]

lemma final_aux (p : ℕ) [Fact p.Prime] [CharP D p] [Algebra.IsAlgebraic k D]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := l2 p ha hinsep
  use m
  constructor
  · exact hm.1
  · intro n hn
    have inter1 : (δ a) ^ (p ^ m) = (f a) ^ (p ^ m) - (g a) ^ (p ^ m) :=
      sub_pow_char_pow_of_commute (D →ₗ[k] D) (f a) (g a) (comm_fg a)
    have inter2 : ∀ x : D, ((δ a) ^ (p ^ m)).1 x = 0 := by
      intro x
      rw [congrArg LinearMap.toAddHom inter1]
      show ((f a) ^ (p ^ m)).1 x - ((g a) ^ (p ^ m)).1 x = 0
      rw [f_pow, g_pow]
      apply sub_eq_zero_of_eq
      suffices h : a ^ (p ^ m) ∈ k by
        rw [Subring.mem_center_iff] at h; exact (h x).symm
      exact hm.2
    have inter3 : (δ a) ^ (p ^ m) = 0 := LinearMap.ext_iff.mpr inter2
    have boring : n = (n - (p ^ m)) + p ^ m := (Nat.sub_eq_iff_eq_add hn).mp rfl
    rw [boring, pow_add, inter3, mul_zero]
