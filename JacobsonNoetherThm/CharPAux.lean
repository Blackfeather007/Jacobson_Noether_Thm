import Mathlib
import JacobsonNoetherThm.AlgebraInstance

#check isPurelyInseparable_iff_pow_mem

variable {D : Type*} [DivisionRing D] [Fact (Nat.Prime p)]

local notation "k" => (Subring.center D)

#check IsPurelyInseparable
#check expChar_prime

instance : Field k := inferInstance

#check IntermediateField.adjoin

lemma aux0 [CharP D p] :
  ∀ a : D, a ∉ k → ∃ m ≥ 1, a ^ (p ^ m) ∈ k := sorry

def δ (a : D) : D → D := fun x ↦ a * x - x * a

lemma finial_aux [CharP D p] (a : D) (a_nin_k : a ∉ k) :
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
