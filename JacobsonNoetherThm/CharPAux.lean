import Mathlib
import JacobsonNoetherThm.AlgebraInstance

variable {D : Type*} [DivisionRing D] [Fact (Nat.Prime p)]

local notation "k" => (Subring.center D)

-- #check IsPurelyInseparable
-- #check expChar_prime
-- #check IntermediateField.adjoin
-- #check isPurelyInseparable_iff_pow_mem

instance : Field k := inferInstance

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

instance [CharP D p] : CharP k p := inferInstance

instance [CharP D p] : CharP (Module.End k D) p := by
  refine { cast_eq_zero_iff' := ?cast_eq_zero_iff' }
  sorry

lemma final_aux [CharP D p] (a : D) (a_nin_k : a ∉ k) :
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := aux0 a a_nin_k (p := p)
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
