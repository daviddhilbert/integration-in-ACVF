import Integration7.SpecialPullbackVolumeObjects
import Integration7.PullbackUnaryChainVolumeComparison

/-! Actual special preparation of a pullback preserves its volume
blowup class, retaining the original nonconstant density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem special_pullback_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a} {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (T : SpecialBijection A B) (hAP : IsRVPullback (carrier A)) (hBP : IsRVPullback (carrier B))
    (hfinA : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      (specialPullbackVolumeGammaObject hc C Ξ T hBP hfinA δ hδ) := by
  intro G
  let π := specialRetainedVolumeForm hc T δ hδ
  let t := specialUnaryChain (Nat.zero_lt_succ n) T.chain
  have hDensity : ∀ p, ω.value p = π.value ((rawSpecialMap hc T.toMap) p) := by
    intro p
    rw [hω]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  have hData : unaryChainVolumeData hc t ω π := special_unary_chain_volume_data hc C T ω π hDensity
  exact pullback_unary_chain_volume_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1 A B hAP hBP hfinA
    (special_target_finite_labels C Ξ T hfinA) hAF (special_pullback_volume_finite C Ξ T hBP hfinA)
    ω π δ (suffixIndex (special_chain_rvArity_le T.chain) δ) hω (fun _ => rfl) t hData

end IntegrationInACVF.Section7
