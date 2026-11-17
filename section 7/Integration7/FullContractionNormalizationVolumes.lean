module

public import Integration7.SmallDimensionContractionNormalization
public import Integration7.GammaEssentialVolumeGraphs
public import Integration7.GammaVolumeDensityRescaling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual raw-to-normalized contraction is a full volume
isomorphism in a genuine context, without an RV dimension restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.essential
  SpecialTransformations.Section9.rvFiniteEssential SpecialTransformations.Section9.rvEssential
  SpecialTransformations.Section4.RVObject.restrict rawUnitVolumeContraction normalizedUnitVolumeContraction
  canonicalNormalizedFiniteContraction canonicalRVObject
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {k a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : DefSet (M := M) (C.base : Set M) (k+1) a} {σ : Equiv.Perm (Fin (k+1))}
variable (T : StandardContraction A σ)
variable (hF : (canonicalRVObject hc T.contractionObject).volume.FiniteFibres)

def fullContractionNormalizationVolumeIso :
    RVVolumeIso (rawUnitVolumeContraction hc T hF) (normalizedUnitVolumeContraction hc T hF) :=
  RVVolumeIso.of_preserving_coordinates_full hc C (canonicalFiniteNormalizationIso hc T hF)
    (canonical_finite_normalization_volume hc T hF) (fun _ => rfl)

set_option maxHeartbeats 600000 in
theorem full_contraction_normalization_volume_iso_gamma (hT : GammaSetDefinable P (carrier T.target)) :
    (fullContractionNormalizationVolumeIso hc C T hF).GammaDefinable P := by
  have hSource := gamma_raw_contraction_domain T hT
  have hCoord : RVMapGamma (rawUnitVolumeContraction hc T hF).underlying.obj.volume P :=
    gamma_real_rv_map_graph hc P _ (rvCoordinateSelectMap P.real T.volumeIndex) hSource (fun _ => rfl)
  have hEssential := gamma_essential_volume_domain (rawUnitVolumeContraction hc T hF) hCoord
  have hGraph := canonical_finite_normalization_gamma hc T hF hT
  exact gamma_volume_iso_of_preserving_coordinates_full hc C
    (U := rawUnitVolumeContraction hc T hF) (V := normalizedUnitVolumeContraction hc T hF)
    (canonicalFiniteNormalizationIso hc T hF)
    (canonical_finite_normalization_volume hc T hF) (fun _ => rfl)
    hEssential hGraph

theorem full_contraction_normalization_constant_density_comparison
    (hT : GammaSetDefinable P (carrier T.target))
    (η : RV (M := M)) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    ∃ e : RVVolumeIso ((rawUnitVolumeContraction hc T hF).rescale η hη hη0)
      ((normalizedUnitVolumeContraction hc T hF).rescale η hη hη0), e.GammaDefinable P :=
  ⟨(fullContractionNormalizationVolumeIso hc C T hF).rescale η hη hη0,
    (full_contraction_normalization_volume_iso_gamma hc C T hF hT).rescale η hη hη0⟩

end IntegrationInACVF.Section7
