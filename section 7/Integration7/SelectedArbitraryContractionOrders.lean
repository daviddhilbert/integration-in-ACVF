module

public import Integration7.SelectedCommonHeadOrderComparison
public import IntegrationSection6.ContractionOrderBridge

@[expose] public section

/-! Arbitrary-order independence with all selected RV volume coordinates
and arbitrary retained density. The induction uses the proved selected
first-two exchange and no Section 5.8 input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 2400000 in
theorem selected_volume_contraction_order_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    SelectedVolumeOrderIndependent hc C Ξ n := by
  induction n with
  | zero =>
    intro a d A ρ δ hδ hfin σ υ T E
    have hOrder : υ = σ := by
      apply Equiv.ext
      intro j
      apply Fin.ext
      have hυ := (υ j).isLt
      have hσ := (σ j).isLt
      omega
    subst υ
    exact selected_same_order_standard_volume_comparison hc C Ξ hΞ γ hγ hγ1 A ρ hfin δ hδ T E
  | succ n ih =>
    intro a d A ρ δ hδ hfin σ υ T E
    by_cases h0 : σ 0 = υ 0
    · exact selected_common_head_order_comparison hc C Ξ hΞ hGenerated γ hγ hγ1 ih
        A ρ δ hδ hfin σ υ h0 T E
    · let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
      have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
      obtain ⟨π,hπ0,hπ1⟩ := exists_contraction_bridge_order σ υ h0
      obtain ⟨D,hD,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
        C.small hGenerated (Set.Subset.refl _) A hA π
      obtain ⟨F,hF,_,_,_⟩ := generated_base_standard_contraction_exists (B := G) C.saturated C.model00
        C.small hGenerated (Set.Subset.refl _) A hA ((swapFirstTwo n).trans π)
      have hLeft := selected_common_head_order_comparison hc C Ξ hΞ hGenerated γ hγ hγ1 ih
        A ρ δ hδ hfin σ π hπ0.symm T D
      have hFirst : ((swapFirstTwo n).trans π) 0 = υ 0 := by
        change π (swapFirstTwo n 0) = υ 0
        rw [swapFirstTwo_zero]
        exact hπ1
      have hRight := selected_common_head_order_comparison hc C Ξ hΞ hGenerated γ hγ hγ1 ih
        A ρ δ hδ hfin ((swapFirstTwo n).trans π) υ hFirst F E
      have hMiddle := selected_first_two_standard_volume_exchange hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        A ρ hfin δ hδ
        (by change π (swapFirstTwo n 0) = π (0 : Fin (n+1)).succ; rw [swapFirstTwo_zero])
        (by change π (swapFirstTwo n (0 : Fin (n+1)).succ) = π 0; rw [swapFirstTwo_one])
        (fun j => by change π (swapFirstTwo n j.succ.succ) = π j.succ.succ; rw [swapFirstTwo_tail]) D F
      exact hLeft.trans hc (hMiddle.trans hc hRight)

end IntegrationInACVF.Section7
