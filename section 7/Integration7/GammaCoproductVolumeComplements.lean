import Integration7.GammaEssentialVolumeEmbeddings
import Integration7.VolumeCoproductComplements

/-! Removing the left essential tagged image leaves the right volume
object with its full original-Gamma comparison chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_coprod_left_complement_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (volumeCoprodLeftComplementIso hc C U V).GammaDefinable B := by
  let T := U.coprod V
  let A := (coprodEssentialLeftMap U V).image
  let D := T.restrict (T.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let R := (coprodEssentialRightMap U V).image
  have hAΓ := (gamma_coprod_essential_left_map hc U V hU).image
  have hRΓ := (gamma_coprod_essential_right_map hc U V hV).image
  have hDΓ : VolumeObjectGamma D B := (hU.coprod hV).restrict (T.underlying.obj.domain.sdiff A) Set.sdiff_subset
    ((gammaLogicInput B).sdiff (hU.coprod hV).coordinates.domain hAΓ)
  have hRD : R.carrier ⊆ D.underlying.obj.domain.carrier := by
    rintro x ⟨v,rfl⟩
    refine ⟨rvEssentialLabels_subset T.underlying.obj (coprodEssentialRightMap U V v).property,?_⟩
    rintro ⟨u,he⟩
    apply Set.disjoint_left.mp (rvTaggedImages_disjoint U.underlying.obj.domain V.underlying.obj.domain)
    · exact ⟨⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩,he⟩
    · exact ⟨⟨v.val,rvEssentialLabels_subset V.underlying.obj v.property⟩,rfl⟩
  have hess : D.essential.obj.domain.carrier ⊆ R.carrier := by
    intro x hx
    let w : T.essential.obj.domain := ⟨x,essentialRestriction_subset T _ Set.sdiff_subset hx⟩
    rcases coprodEssential_cover U V w with ⟨u,hu⟩ | ⟨v,hv⟩
    · exact False.elim (hx.1.2 ⟨u,congrArg (fun p : T.essential.obj.domain => p.val) hu⟩)
    · exact ⟨v,congrArg (fun p : T.essential.obj.domain => p.val) hv⟩
  let e := volumeIsoOfContainingEssentialRestriction hc C D R hRD hess
  have he : e.GammaDefinable B := gamma_containing_essential_restriction_iso hc C D hDΓ R hRD hess hRΓ
  change ((e.symm hc C).trans hc C ((volumeCoprodRightImageIso hc C U V).symm hc C)).GammaDefinable B
  exact (he.symm hc C B).trans hc C B ((gamma_volume_coprod_right_image_iso hc C U V hV).symm hc C B)

end IntegrationInACVF.Section7
