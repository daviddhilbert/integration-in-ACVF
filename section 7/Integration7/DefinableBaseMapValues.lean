module

public import Integration7.NamedMapValueDefinability

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Output coordinates of actual VF and RV maps are definable over any
base over which all input coordinates are definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {n m : ℕ}

theorem vf_map_value_coordinate_definable
    {A : DefSet (rawVFSpace (M := M) n) S} {B : DefSet (rawVFSpace (M := M) m) S}
    (f : Map A B) (x : A) (hx : ∀ i, S.Definable₁ LRV {(x.val i).val}) (j : Fin m) :
    S.Definable₁ LRV {((f x).val j).val} := by
  have h := map_singleton_definable f x (raw_vf_singleton_definable x.val hx)
  change S.Definable LRV _ at h
  rw [raw_vf_singleton_preimage] at h
  exact tuple_singleton_coordinate_definable h j

theorem vf_rv_map_value_coordinate_definable
    {A : DefSet (rawVFSpace (M := M) n) S} {B : DefSet (rawRVSpace (M := M) m) S}
    (f : Map A B) (x : A) (hx : ∀ i, S.Definable₁ LRV {(x.val i).val}) (j : Fin m) :
    S.Definable₁ LRV {((f x).val j).val} := by
  have h := map_singleton_definable f x (raw_vf_singleton_definable x.val hx)
  change S.Definable LRV _ at h
  rw [raw_rv_singleton_preimage] at h
  exact tuple_singleton_coordinate_definable h j

end IntegrationInACVF.Section7
