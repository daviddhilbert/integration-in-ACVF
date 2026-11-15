import Integration7.PreparedSubdomainVolumeGluing
import Integration7.SpecialPullbackVolumeComparisons
import Integration7.NativeVolumeMapRealization
import Integration7.VFVolumeIsomorphisms

/-! The common-blowup kernel for an actual almost-everywhere VF volume
isomorphism between RV-pullbacks, including the discarded complements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem pullback_volume_ae_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hAP : IsRVPullback (carrier A)) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hfinB : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier B}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : VFVolumeIso (nativeMixedVFVolumeObject hc A hfinA ω) (nativeMixedVFVolumeObject hc B hfinB π)) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) B
        ((gammaLogicInput G).real_set _ (setDefinable B)) hBF ε hε) := by
  classical
  intro G
  let L := nativeMixedVolumeDomain hc f.source
  let K := nativeMixedVolumeDomain hc f.target
  have hLA : carrier L ⊆ carrier A := f.source_subset
  have hKB : carrier K ⊆ carrier B := f.target_subset
  let ωL : VolumeForm (rawSpecialSet hc L) := ω.restrict hLA
  let πK : VolumeForm (rawSpecialSet hc K) := π.restrict hKB
  let g : Map L K := nativeMixedVolumeMap hc f.bijection.map
  obtain ⟨Q⟩ := native_volume_unary_partition_exists hc C Ξ hNames γ hγ1 g
    (native_mixed_volume_map_bijective hc f.bijection.map f.bijection.bijective) ωL πK f.bijection.preserves
  letI := Q.finite
  obtain ⟨P⟩ := native_prepared_mixed_partition_exists C Ξ hGenerated A hAP (nativeCompletedPartition A L Q.source)
    (native_completed_partition_subset A L Q.source hLA Q.sourceSubset)
    (native_completed_partition_disjoint A L Q.source Q.sourceSubset Q.sourceDisjoint)
    (native_completed_partition_cover A L Q.source hLA Q.sourceSubset Q.sourceCover)
  obtain ⟨R⟩ := native_prepared_mixed_partition_exists C Ξ hGenerated B hBP (nativeCompletedPartition B K Q.target)
    (native_completed_partition_subset B K Q.target hKB Q.targetSubset)
    (native_completed_partition_disjoint B K Q.target Q.targetSubset Q.targetDisjoint)
    (native_completed_partition_cover B K Q.target hKB Q.targetSubset Q.targetCover)
  have hLeft := special_pullback_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1 P.special
    hAP P.pullback hfinA hAF ω δ hω hδ
  have hRight := special_pullback_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1 R.special
    hBP R.pullback hfinB hBF π ε hπ hε
  have hMiddle := prepared_subdomain_volume_gluing hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    hLA hKB ω π δ ε hω hπ hδ hε hfinA hfinB
    f.source_complement_small f.target_complement_small Q P R
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end IntegrationInACVF.Section7
