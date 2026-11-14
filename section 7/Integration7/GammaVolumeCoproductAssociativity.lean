import Integration7.GammaVolumeCoproductCoherence

/-! The existing actual volume associator retains its full original
Gamma graph. The three tagged branches are tracked explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_coprod_assoc
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hW : VolumeObjectGamma W B) :
    (volumeCoprodAssoc hc C U V W).GammaDefinable B := by
  let F := (rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
  let fl := F.comp (rvCoprodLeftMap (U.coprod V).underlying.obj W.underlying.obj)
  let outer := rvRightTagMap (V.coprod W).underlying.obj.domain U.underlying.obj.arity
  have hOuter : RVMapGamma outer B := gamma_rv_right_tag_map hc _ _ (hV.coprod hW).coordinates.domain
  have hVleft : RVMapGamma (rvCoprodLeftMap V.underlying.obj W.underlying.obj) B :=
    (gamma_rv_left_tag_map hc _ _ hV.coordinates.domain).congr (fun _ => rfl)
  have hWright : RVMapGamma (rvCoprodRightMap V.underlying.obj W.underlying.obj) B :=
    (gamma_rv_right_tag_map hc _ _ hW.coordinates.domain).congr (fun _ => rfl)
  have hfl : RVMapGamma fl B := by
    apply gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj fl
      (rvLeftTagMap U.underlying.obj.domain (V.coprod W).underlying.obj.arity)
      (outer.comp (rvCoprodLeftMap V.underlying.obj W.underlying.obj))
      (gamma_rv_left_tag_map hc _ _ hU.coordinates.domain) (hVleft.comp hOuter)
    · intro u
      exact congrArg Subtype.val (rvCoprodAssocExplicit_left U.underlying.obj V.underlying.obj W.underlying.obj u)
    · intro v
      exact congrArg Subtype.val (rvCoprodAssocExplicit_middle U.underlying.obj V.underlying.obj W.underlying.obj v)
  have hF : RVMapGamma F B := by
    apply gamma_tagged_rv_map_graph (U.coprod V).underlying.obj W.underlying.obj F
      fl.toUniv (outer.comp (rvCoprodRightMap V.underlying.obj W.underlying.obj))
      (hfl.congr (fun _ => rfl)) (hWright.comp hOuter)
    · intro u
      rfl
    · intro w
      exact congrArg Subtype.val (rvCoprodAssocExplicit_right U.underlying.obj V.underlying.obj W.underlying.obj w)
  exact gamma_volume_iso_of_full_map _ F
    (gamma_essential_volume_domain _ ((hU.coprod hV).coprod hW).coordinates) hF (fun _ => rfl)

end IntegrationInACVF.Section7
