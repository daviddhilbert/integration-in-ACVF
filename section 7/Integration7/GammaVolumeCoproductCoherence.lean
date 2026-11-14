import Integration7.GammaRVTagMaps
import Integration7.GammaVolumeObjectCoproducts
import Integration7.GammaVolumeFullChartRestriction
import Integration7.VolumeCoproductAssociativity

/-! The existing volume identity and coproduct swap have full original
Gamma graphs on actual Gamma volume objects. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem VolumeObjectGamma.identity_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) : (RVVolumeIso.refl hc C U).GammaDefinable B := by
  have h : RVMapGamma (Map.id U.essential.obj.domain) B :=
    RVMapGamma.identity hc (gamma_essential_volume_domain U hU.coordinates)
  exact h.congr (fun _ => rfl)

theorem gamma_volume_coprod_swap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (volumeCoprodSwap hc C U V).GammaDefinable B := by
  let F := (rvCoprodSwapExplicit U.underlying.obj V.underlying.obj).hom.map
  have hF : RVMapGamma F B := gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj F
    (rvRightTagMap U.underlying.obj.domain V.underlying.obj.arity)
    (rvLeftTagMap V.underlying.obj.domain U.underlying.obj.arity)
    (gamma_rv_right_tag_map hc _ _ hU.coordinates.domain)
    (gamma_rv_left_tag_map hc _ _ hV.coordinates.domain)
    (fun u => congrArg Subtype.val (rvCoprodSwapExplicit_left U.underlying.obj V.underlying.obj u))
    (fun v => congrArg Subtype.val (rvCoprodSwapExplicit_right U.underlying.obj V.underlying.obj v))
  exact gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ (hU.coprod hV).coordinates) hF (fun _ => rfl)

end IntegrationInACVF.Section7
