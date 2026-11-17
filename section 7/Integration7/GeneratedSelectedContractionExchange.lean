module

public import Integration7.GeneratedOrdinaryContractionExchange
public import Integration7.OrdinarySelectedTailContractionCharts
public import Integration7.SelectedVFTailFirstTwoOrders
public import IntegrationSection6.GammaOrdinaryContractionPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! First-two contraction exchange with arbitrary retained RV labels
over the standing generated base. Realize the labels by VF tails, use
ordinary exchange, and descend through the full ordinary label charts.
Zero labels are retained throughout; no volume-essentialization is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a d : ℕ}

theorem selected_vf_tail_swap_first_two (σ : Equiv.Perm (Fin (n+2))) :
    selectedVFTailPermutation d ((swapFirstTwo n).trans σ) =
      (swapFirstTwo (d+n)).trans (selectedVFTailPermutation d σ) := by
  have h0 : ((swapFirstTwo n).trans σ) 0 = σ (0 : Fin (n+1)).succ := by
    change σ (swapFirstTwo n 0) = _
    rw [swapFirstTwo_zero]
  have h1 : ((swapFirstTwo n).trans σ) (0 : Fin (n+1)).succ = σ 0 := by
    change σ (swapFirstTwo n (0 : Fin (n+1)).succ) = _
    rw [swapFirstTwo_one]
  have ht : ∀ j : Fin n, ((swapFirstTwo n).trans σ) j.succ.succ = σ j.succ.succ := by
    intro j
    change σ (swapFirstTwo n j.succ.succ) = _
    rw [swapFirstTwo_tail]
  obtain ⟨h0',h1',ht'⟩ := selected_vf_tail_first_two_orders (d := d) σ _ h0 h1 ht
  apply Equiv.ext
  intro j
  change selectedVFTailPermutation d ((swapFirstTwo n).trans σ) j =
    selectedVFTailPermutation d σ (swapFirstTwo (d+n) j)
  cases j using Fin.cases with
  | zero => rw [swapFirstTwo_zero]; exact h0'
  | succ j =>
    cases j using Fin.cases with
    | zero => rw [swapFirstTwo_one]; exact h1'
    | succ j => rw [swapFirstTwo_tail]; exact ht' j

set_option maxHeartbeats 2000000 in
theorem generated_selected_first_two_exchange {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+2))}
    (T : StandardContraction U σ) (E : StandardContraction U ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (P : GammaSelectedRVPresentation B T.target (orderedSelectedIndex T.program ρ))
    (Q : GammaSelectedRVPresentation B E.target (orderedSelectedIndex E.program ρ)) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage U hU σ) hT ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage U hU ((swapFirstTwo n).trans σ)) hE ρ
  let A' := nativeProgramSelectedRVVFTailLift hc U ρ
  let R := selectedRVVFTailStandardContraction hc T ρ F
  let Z := selectedRVVFTailStandardContraction hc E ρ H
  have hA' : GammaSetDefinable B (carrier A') := gamma_native_program_selected_rv_vf_tail_lift hc U ρ hU
  have hfin' : ∀ x : Fin (d+n+2) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A'}.Finite :=
    native_program_selected_rv_vf_tail_finite_labels hc U ρ hfin
  have hR : GammaProgramDefinable B R.program :=
    gamma_selected_rv_vf_tail_standard_contraction hc T ρ F hFullF
  have hZ : GammaProgramDefinable B Z.program :=
    gamma_selected_rv_vf_tail_standard_contraction hc E ρ H hFullH
  have hOrd := generated_ordinary_first_two_exchange_of_order hκ hs h00 hreal hgamma hGenerated
    δ hδ hδ1 hBS A' hA' hfin' (selected_vf_tail_swap_first_two σ) R Z hR hZ
  obtain ⟨PR⟩ := gammaSelectedRVPresentation_exists R.target (gamma_program_final_set R.program hR)
    (orderedSelectedIndex R.program (Fin.elim0 : Fin 0 → Fin a))
    (ordered_selected_fibres_finite hκ.le hs hreal R.program hR Fin.elim0
      (empty_selected_fibres (vfPermutationImage A' (selectedVFTailPermutation d σ))
        (vfPermutation_finite_rv_fibres A' _ hfin')))
  obtain ⟨PZ⟩ := gammaSelectedRVPresentation_exists Z.target (gamma_program_final_set Z.program hZ)
    (orderedSelectedIndex Z.program (Fin.elim0 : Fin 0 → Fin a))
    (ordered_selected_fibres_finite hκ.le hs hreal Z.program hZ Fin.elim0
      (empty_selected_fibres (vfPermutationImage A' (selectedVFTailPermutation d ((swapFirstTwo n).trans σ)))
        (vfPermutation_finite_rv_fibres A' _ hfin')))
  have hCast := hOrd.castDegree (orderedVolumeDegree_eq (d+(n+2)) 0).symm
  have hPRPZ := hCast.corollary_6_6
    (gammaOrdinaryContractionPresentationIso hκ.le hs hreal hBS hA' hfin' R hR PR)
    (gammaOrdinaryContractionPresentationIso hκ.le hs hreal hBS hA' hfin' Z hZ PZ)
  let iR := selectedTailOrdinaryContractionIso hc T ρ F hFVF hFCon (gamma_program_final_set F hF) PR P
  let iZ := selectedTailOrdinaryContractionIso hc E ρ H hHVF hHCon (gamma_program_final_set H hH) PZ Q
  have hTail := hPRPZ.corollary_6_6 (gammaIsoSymm iR) (gammaIsoSymm iZ)
  have hFinal := hTail.castDegree (selected_tail_ordinary_degree_eq (d := d) (n := n+2))
  simpa only [gammaCastDegree_symm] using hFinal
end IntegrationInACVF.Section7
