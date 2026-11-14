import Integration7.GammaChartedVolumeBlowups
import Integration7.GammaCanonicalVolumeComparison
import Integration7.GammaActualVolumePartitions
import Integration7.GammaVolumeRestrictionIdentities
import Integration7.ElementaryBlowupPartitions

/-! Full original-Gamma elementary charts admit Gamma canonicalization
and Gamma partition isomorphisms, including complementary labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem exists_gamma_canonical_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U W) (hU : VolumeObjectGamma U B) (hW : VolumeObjectGamma W B)
    (hFull : RVMapGamma b.packedChartMap B) :
    ∃ e : RVVolumeIso (elementaryVolumeObject C U b.admissible) W, e.GammaDefinable B := by
  apply exists_gamma_elementaryBlowupIso hc C B (RVVolumeIso.refl hc C U)
    (elementaryVolumeBlowup C U b.admissible) b hU.coordinates hU.coordinates hU.density hU.density
    (hU.identity_iso hc C)
  · exact gamma_canonical_packed_elementary_chart hc C B U b.admissible
      (gamma_elementary_volume_coordinates hc C U b.admissible hU.coordinates)
  · exact b.gamma_essential_packed_chart hW hFull

set_option maxHeartbeats 800000 in
theorem exists_gamma_partition_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U W) (hU : VolumeObjectGamma U B) (hW : VolumeObjectGamma W B)
    (hFull : RVMapGamma b.packedChartMap B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    ∃ e : RVVolumeIso
      ((elementaryVolumeObject C (U.restrict A hA) (b.admissible.restrict A hA)).coprod
        (elementaryVolumeObject C (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)
          (b.admissible.restrict _ Set.sdiff_subset))) W, e.GammaDefinable B := by
  let R := U.underlying.obj.domain.sdiff A
  have hRΓ := (gammaLogicInput B).sdiff hU.coordinates.domain hAΓ
  let PA := b.sourcePreimage A
  let PR := b.sourcePreimage R
  have hPAΓ := b.gamma_source_preimage hc hFull A hAΓ
  have hPRΓ := b.gamma_source_preimage hc hFull R hRΓ
  obtain ⟨eL,heL⟩ := (b.restrict A hA).exists_gamma_canonical_iso hc C
    (hU.restrict A hA hAΓ) (hW.restrict PA (b.sourcePreimage_subset A) hPAΓ)
    (b.gamma_restricted_packed_chart hc hFull A hA hAΓ)
  obtain ⟨eR,heR⟩ := (b.restrict R Set.sdiff_subset).exists_gamma_canonical_iso hc C
    (hU.restrict R Set.sdiff_subset hRΓ) (hW.restrict PR (b.sourcePreimage_subset R) hPRΓ)
    (b.gamma_restricted_packed_chart hc hFull R Set.sdiff_subset hRΓ)
  let ecomp := volumeRestrictionCarrierIso hc C W PR (W.underlying.obj.domain.sdiff PA)
    (b.sourcePreimage_subset R) Set.sdiff_subset (b.sourcePreimage_complement A)
  have hcomp : ecomp.GammaDefinable B := gamma_volume_restriction_carrier_iso hc C W hW PR _
    (b.sourcePreimage_subset R) Set.sdiff_subset (b.sourcePreimage_complement A) hPRΓ
  let part := volumeComplementPartitionIso hc C W PA (b.sourcePreimage_subset A)
  have hpart : part.GammaDefinable B := gamma_actual_volume_complement_partition hc C W hW PA
    (b.sourcePreimage_subset A) hPAΓ
  refine ⟨(eL.coprod hc C (eR.trans hc C ecomp)).trans hc C part,?_⟩
  exact (heL.coprod hc C B (heR.trans hc C B hcomp)).trans hc C B hpart

end IntegrationInACVF.Section7.ElementaryBlowup
