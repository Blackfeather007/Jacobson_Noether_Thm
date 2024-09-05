import Mathlib
import JacobsonNoetherThm.AlgebraInstance

#check isPurelyInseparable_iff_pow_mem

variable {D : Type*} [DivisionRing D] [Fact (Nat.Prime p)]

local notation "k" => (Subring.center D)

#check IsPurelyInseparable
#check expChar_prime

instance : Field k := inferInstance

#check IntermediateField.adjoin

lemma aux0 [ExpChar k p] :
  ∀ a : D, a ∉ (algebraMap k D).range → ∃ m ≥ 1, a ^ (p ^ m) ∈ k := sorry

def f (a : D) : D → D := fun x ↦ a * x

def g (a : D) : D → D := fun x ↦ x * a

def δ (a : D) : D → D := f a - g a

lemma finial_aux (a : D) (a_nin_k : a ∉ (algebraMap k D).range) :
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := sorry