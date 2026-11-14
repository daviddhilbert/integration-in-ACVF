import Integration7.PullbackCoordinateVolumeObjects
import Integration7.VolumePartition
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeComposition
import Integration7.RVVolumeInverse
import IntegrationSection6.PullbackPartitions

/-! Disjoint pullback pieces partition the actual canonical volume
object, preserving its retained density as well as every coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (pullbackObject rvObjectVolume carrier IsRVPullback)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def pullbackVolumePartitionIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A L R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hLF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject L)))
    (hRF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject R)))
    (hPart : carrier A = carrier L ∪ carrier R) (hDisj : Disjoint (carrier L) (carrier R))
    (hLP : IsRVPullback (carrier L)) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    RVVolumeIso
      ((pullbackCoordinateVolumeObject hc L hLF δ
        (fun p => hδ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inl p.property)⟩)).coprod
       (pullbackCoordinateVolumeObject hc R hRF δ
        (fun p => hδ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inr p.property)⟩)))
      (pullbackCoordinateVolumeObject hc A hAF δ hδ) := by
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
  exact ((iL.symm hc C).coprod hc C (iR.symm hc C)).trans hc C (volumeComplementPartitionIso hc C U D hD)

end IntegrationInACVF.Section7
