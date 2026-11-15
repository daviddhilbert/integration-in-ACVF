import Integration7.PullbackOriginalVolumeClasses
import Integration7.UnaryChainVolumeContractions

/-! Actual pullback RV volume objects compare whenever their VF domains
are joined by a genuine volume-preserving unary factor chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem pullback_unary_chain_volume_comparison
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
    (T : UnaryChain (C.base : Set M) (n+1) A B) (hData : unaryChainVolumeData hc T ω π) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    let hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero ⟨p.val,p.property⟩ ((hπ ⟨p.val,p.property⟩).trans hz))
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) B
        ((gammaLogicInput G).real_set _ (setDefinable B)) hBF ε hε) := by
  intro G hδ hε
  let U := nativeMixedVFVolumeObject hc A hfinA ω
  let V := nativeMixedVFVolumeObject hc B hfinB π
  let A' := nativeMixedVolumeDomain hc U.densityGraph.domain
  let B' := nativeMixedVolumeDomain hc V.densityGraph.domain
  have hA' : GammaSetDefinable G (carrier A') := (gammaLogicInput G).real_set _ (setDefinable A')
  have hB' : GammaSetDefinable G (carrier B') := (gammaLogicInput G).real_set _ (setDefinable B')
  obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) A' hA' (Equiv.refl _)
  obtain ⟨E,hE,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
    C.small hGenerated (Set.Subset.refl _) B' hB' (Equiv.refl _)
  have hLeft := pullback_original_volume_contraction_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    A hAP hfinA hAF ω δ hω D
  have hRight := pullback_original_volume_contraction_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    B hBP hfinB hBF π ε hπ E
  have hMiddle := unary_chain_volume_contractions_compare hc C Ξ hΞ hGenerated hNames γ hγ hγ1 T
    ω π hData hfinA hfinB D E
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end IntegrationInACVF.Section7
