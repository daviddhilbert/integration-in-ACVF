module

public import Integration7.PreparedVolumePartitionGluing
public import Integration7.SpecialPullbackVolumeComparisons

@[expose] public section

/-! The volume lift kernel for actual RV-pullbacks and a full
volume-preserving bijection, proved by the genuine Section 5.6 partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem pullback_volume_bijection_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hAP : IsRVPullback (carrier A)) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject B)))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b) (hω : ∀ p, ω.value p = p.val.2 δ) (hπ : ∀ p, π.value p = p.val.2 ε)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (f : Map A B) (hf : Function.Bijective f)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f)) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) B
        ((gammaLogicInput G).real_set _ (setDefinable B)) hBF ε hε) := by
  classical
  intro G
  have hfinB := finite_rv_fibres_of_gamma_bijection (B := G) C.uncountable.le C.saturated C.small
    f hf ((gammaLogicInput G).real_map_graph f) hfinA
  obtain ⟨Q⟩ := native_volume_unary_partition_exists hc C Ξ hNames γ hγ1 f hf ω π hm
  letI := Q.finite
  obtain ⟨P⟩ := native_prepared_mixed_partition_exists C Ξ hGenerated A hAP Q.source
    Q.sourceSubset Q.sourceDisjoint Q.sourceCover
  obtain ⟨R⟩ := native_prepared_mixed_partition_exists C Ξ hGenerated B hBP Q.target
    Q.targetSubset Q.targetDisjoint Q.targetCover
  have hLeft := special_pullback_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1 P.special
    hAP P.pullback hfinA hAF ω δ hω hδ
  have hRight := special_pullback_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1 R.special
    hBP R.pullback hfinB hBF π ε hπ hε
  have hMiddle := prepared_volume_partition_gluing hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    ω π δ ε hω hπ hδ hε hfinA hfinB Q P R
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end IntegrationInACVF.Section7
