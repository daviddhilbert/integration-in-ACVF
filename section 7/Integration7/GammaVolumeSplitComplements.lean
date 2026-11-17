module

public import Integration7.GammaActualVolumePartitions
public import Integration7.VolumeComplementPartitions
public import Integration7.GammaVolumeCoproductCharts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual three-piece complementary splitting retains the full
original-Gamma chart of every cut. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_split_complement
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A D : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hD : D.carrier ⊆ U.underlying.obj.domain.carrier)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier})
    (hDΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ D.carrier}) :
    (volumeSplitComplement hc C U A D hD).GammaDefinable B := by
  let R := U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let Q := D.sdiff A
  let E := R.underlying.obj.domain.sdiff Q
  have hRcut := (gammaLogicInput B).sdiff hU.coordinates.domain hAΓ
  have hR : VolumeObjectGamma R B := hU.restrict _ Set.sdiff_subset hRcut
  have hQ := (gammaLogicInput B).sdiff hDΓ hAΓ
  have hE := (gammaLogicInput B).sdiff hR.coordinates.domain hQ
  unfold volumeSplitComplement
  apply RVVolumeIso.GammaDefinable.trans hc C B
  · apply RVVolumeIso.GammaDefinable.symm hc C B
    exact gamma_actual_volume_complement_partition hc C R hR Q _ hQ
  · apply RVVolumeIso.GammaDefinable.coprod hc C B
    · exact gamma_volume_restriction_trans_iso hc C U hU _ Q _ _ hRcut hQ
    · apply RVVolumeIso.GammaDefinable.trans hc C B
      · exact gamma_volume_restriction_trans_iso hc C U hU _ E _ _ hRcut hE
      · exact gamma_volume_restriction_carrier_iso hc C U hU E _ _ _ _ hE

end IntegrationInACVF.Section7
