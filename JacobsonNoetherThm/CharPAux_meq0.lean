import Mathlib
import JacobsonNoetherThm.AlgebraInstance

#check isPurelyInseparable_iff_pow_mem

variable {D : Type*} [DivisionRing D] [Fact (Nat.Prime p)]

local notation "k" => (Subring.center D)

#check IsPurelyInseparable
#check expChar_prime

instance : Field k := inferInstance

#check IntermediateField.adjoin

lemma aux0 [CharP D p] (hInsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∀ a : D, a ∉ k → ∃ m ≥ 1, a ^ (p ^ m) ∈ k := by
    intro a ha
    have hCharP: CharP k p := sorry
    have hIrr : Irreducible (minpoly k a) := sorry
    have hpne0 : p ≠ 0 := sorry
    have hpow := Polynomial.exists_separable_of_irreducible p hIrr hpne0
    rcases hpow with ⟨m, ⟨ϕ, hϕ, hpow⟩⟩
    use m
    by_cases hm : m = 0
    · rw [hm, pow_zero, Polynomial.expand_one] at hpow
      rw [hpow] at hϕ
      have hSep : IsSeparable k ϕ := False.elim (ha (hInsep a hϕ))
      have hSep' : IsSeparable k a := hϕ
      have hInsep' := hInsep a hSep'
      tauto
    · constructor
      · exact Nat.one_le_iff_ne_zero.mpr hm
      · sorry

def f (a : D) : D → D := fun x ↦ a * x

def g (a : D) : D → D := fun x ↦ x * a

def δ (a : D) : D → D := f a - g a

lemma final_aux [CharP D p] (a : D) (a_nin_k : a ∉ (algebraMap k D).range) :
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := sorry
