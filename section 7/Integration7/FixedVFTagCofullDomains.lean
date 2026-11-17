module

public import Integration7.FixedVFLabelTags
public import Integration7.VFCofullSubdomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! RV tagging preserves cofullness, and unions of cofull summands are
cofull in their union. All discarded sets retain smaller VF dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem VFCofull.union
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A B L K : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    (hL : VFCofull A L) (hK : VFCofull B K) : VFCofull (A.union B) (L.union K) := by
  refine ⟨Set.union_subset_union hL.subset hK.subset,?_⟩
  have hsub : ((A.union B).sdiff (L.union K)).carrier ⊆
      ((A.sdiff L).union (B.sdiff K)).carrier := by
    rintro p ⟨hp,hnot⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨hp,fun h => hnot (Or.inl h)⟩
    · exact Or.inr ⟨hp,fun h => hnot (Or.inr h)⟩
  apply (vfDim_mono_same_arity hsub).trans_lt
  rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
  exact max_lt hL.small hK.small

theorem fixed_vf_left_tag_cofull
    {A L : DefSet (rawMixedSpace (M := M) n a) S} (hL : VFCofull A L) (b : ℕ) :
    VFCofull (fixedVFLeftTagMap A b).image (fixedVFLeftTagMap L b).image := by
  have h := hL.image (fixedVFLeftTagMap A b).toImage
    (fixed_vf_left_tag_to_image_bijective A b)
  exact h

theorem fixed_vf_right_tag_cofull
    {B K : DefSet (rawMixedSpace (M := M) n a) S} (hK : VFCofull B K) (b : ℕ) :
    VFCofull (fixedVFRightTagMap B b).image (fixedVFRightTagMap K b).image := by
  have h := hK.image (fixedVFRightTagMap B b).toImage
    (fixed_vf_right_tag_to_image_bijective B b)
  exact h

end IntegrationInACVF.Section7
