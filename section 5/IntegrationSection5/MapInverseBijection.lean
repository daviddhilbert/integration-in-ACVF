import IntegrationSection5.ChainAlgebra

/-! The actual definable inverse is bijective, and its inverse is the original map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem inverse_map_bijective (f : Map A B) (hf : Function.Bijective f) :
    Function.Bijective (Map.inverse f hf) := by
  constructor
  · intro a b he
    have h := congrArg f he
    rw [Map.apply_inverse,Map.apply_inverse] at h
    exact h
  · intro a
    exact ⟨f a,Map.inverse_apply f hf a⟩

theorem inverse_map_inverse_apply (f : Map A B) (hf : Function.Bijective f) (a : A) :
    Map.inverse (Map.inverse f hf) (inverse_map_bijective f hf) a = f a := by
  apply (inverse_map_bijective f hf).1
  rw [Map.apply_inverse,Map.inverse_apply]

theorem inverse_map_inverse_contractible (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) :
    Contractible (Map.inverse (Map.inverse f hf) (inverse_map_bijective f hf)) := by
  intro a b hab
  rw [inverse_map_inverse_apply,inverse_map_inverse_apply]
  exact hc a b hab

end IntegrationInACVF.Section5
