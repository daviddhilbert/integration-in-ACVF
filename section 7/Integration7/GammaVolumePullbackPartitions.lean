module

public import Integration7.GammaVolumeLabelIdentities
public import Integration7.GammaVolumeCoproductCharts
public import Integration7.GammaVolumeComplementPartitions
public import Integration7.VolumePullbackPartitions
public import Integration7.PullbackCoordinateVolumeObjects
public import Integration7.VolumePartition
public import Integration7.VolumeCoproductIsomorphism
public import Integration7.RVVolumeComposition
public import Integration7.RVVolumeInverse
public import IntegrationSection6.PullbackPartitions
public import IntegrationSection6.FiniteGammaPullbackPartitions

@[expose] public section

/-! Pullback partitions preserve the full original-Gamma chart of
the actual volume comparison, including their unchanged density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume rvObjectDomain carrier IsRVPullback GammaSetDefinable)
open IntegrationInACVF.Section6
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k a : ℕ}
variable {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 800000 in
theorem gamma_pullback_volume_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A L R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hLF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject L)))
    (hRF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject R)))
    (hPart : carrier A = carrier L ∪ carrier R) (hDisj : Disjoint (carrier L) (carrier R))
    (hLP : IsRVPullback (carrier L)) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hBS : B.real ⊆ (C.base : Set M))
    (hAΓ : GammaSetDefinable B (carrier A)) (hLΓ : GammaSetDefinable B (carrier L))
    (hRΓ : GammaSetDefinable B (carrier R)) :
    (pullbackVolumePartitionIso hc C A L R hAF hLF hRF hPart hDisj hLP δ hδ).GammaDefinable B := by
  let U := pullbackCoordinateVolumeObject hc A hAF δ hδ
  let V := pullbackCoordinateVolumeObject hc L hLF δ
    (fun p => hδ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inl p.property)⟩)
  let W := pullbackCoordinateVolumeObject hc R hRF δ
    (fun p => hδ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inr p.property)⟩)
  let D := V.underlying.obj.domain
  have hD : D.carrier ⊆ U.underlying.obj.domain.carrier :=
    Section6.pullbackObject_domain_mono (fun p hp => (Set.ext_iff.mp hPart p).mpr (Or.inl hp))
  have hUnion := Section6.pullbackObject_domains_union hPart
  have hApart := Section6.pullbackObject_domains_disjoint hDisj hLP
  have hComplement : (U.underlying.obj.domain.sdiff D).carrier = W.underlying.obj.domain.carrier := by
    ext r
    constructor
    · rintro ⟨hr,hn⟩
      rcases (Set.ext_iff.mp hUnion r).mp hr with h | h
      · exact (hn h).elim
      · exact h
    · intro hr
      exact ⟨(Set.ext_iff.mp hUnion r).mpr (Or.inr hr),fun h => Set.disjoint_left.mp hApart h hr⟩
  let eL : (U.restrict D hD).underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (rvIsoOfCarrierEq _ _ _ _ rfl (fun _ => rfl))
  let eR : (U.restrict (U.underlying.obj.domain.sdiff D) Set.sdiff_subset).underlying ≅ W.underlying :=
    rvFiniteIsoOfAmbient (rvIsoOfCarrierEq _ _ _ _ hComplement (fun _ => rfl))
  let iL := RVVolumeIso.of_preserving_coordinates_full hc C eL (fun _ => rfl) (fun _ => rfl)
  let iR := RVVolumeIso.of_preserving_coordinates_full hc C eR (fun _ => rfl) (fun _ => rfl)
  let UΓ := FiniteRV.gammaPullbackAt hBS A hAΓ hAF
  let VΓ := FiniteRV.gammaPullbackAt hBS L hLΓ hLF
  let LΓ := FiniteRV.gammaRestrictAt UΓ (rvObjectDomain (pullbackObject L)) hD VΓ.domain_graph
  let RΓ := FiniteRV.gammaComplementAt UΓ (rvObjectDomain (pullbackObject L)) VΓ.domain_graph
  have hiL : iL.GammaDefinable B := by
    apply gamma_volume_iso_label_identity B iL
      (gamma_essential_volume_domain (U.restrict D hD) (canonical_gamma_object_volume_graph hc LΓ))
    intro u
    rfl
  have hiR : iR.GammaDefinable B := by
    apply gamma_volume_iso_label_identity B iR
      (gamma_essential_volume_domain (U.restrict (U.underlying.obj.domain.sdiff D) Set.sdiff_subset)
        (canonical_gamma_object_volume_graph hc RΓ))
    intro u
    rfl
  exact ((hiL.symm hc C B).coprod hc C B (hiR.symm hc C B)).trans hc C B
    (gamma_volume_complement_partition hc C UΓ U.form (rvObjectDomain (pullbackObject L)) hD VΓ.domain_graph)

end IntegrationInACVF.Section7
