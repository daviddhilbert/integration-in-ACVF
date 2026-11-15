import Integration7.SelectedVFTailVolumeCharts
import Integration7.SelectedVFTailFirstTwoOrders
import Integration7.RawStandardVolumeNormalization
import Integration7.Lemma77

/-! First-two exchange with arbitrary retained selected RV coordinates.
Realize those coordinates by VF tails, apply the completed Lemma 7.7,
and descend through the actual coordinate- and density-preserving charts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

set_option maxHeartbeats 3200000 in
theorem selected_first_two_standard_volume_exchange
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+2) a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction A σ) (E : StandardContraction A υ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin T⟩
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E⟩ := by
  intro G
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) (gamma_program_over_real_base G T.program) ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage A hA υ) (gamma_program_over_real_base G E.program) ρ
  let A' : DefSet (M := M) (C.base : Set M) (d+n+2) a :=
    nativeProgramSelectedRVVFTailLift (n := n+2) (d := d) hc A ρ
  let T' := selectedRVVFTailStandardContraction hc T ρ F
  let E' := selectedRVVFTailStandardContraction hc E ρ H
  have hA' : GammaSetDefinable G (carrier A') := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  have hfin' : ∀ x : Fin (d+n+2) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A'}.Finite :=
    native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  have hδ' : ∀ p ∈ carrier A', (p.2 δ).val ≠ iRVZero := fun p hp =>
    native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ (fun q => hδ q.val q.property) ⟨p,hp⟩
  obtain ⟨h0',h1',hTail'⟩ := selected_vf_tail_first_two_orders (d := d) σ υ h0 h1 hTail
  have hCompare := lemma_7_7_native hc C (Set.Subset.refl _) hNames hΞ hGenerated γ hγ hγ1
    (fun _ h => h) A' hA' hfin' δ (fun p => hδ' p.val p.property) h0' h1' hTail' T' E'
    (gamma_program_over_real_base G T'.program) (gamma_program_over_real_base G E'.program)
  have hNT := raw_standard_volume_normalization hc C Ξ A' hfin' δ hδ' T'
  have hNE := raw_standard_volume_normalization hc C Ξ A' hfin' δ hδ' E'
  let RT := selectedTailCompletionVolumeObject hc C Ξ A ρ hfin δ hδ T F
  let RE := selectedTailCompletionVolumeObject hc C Ξ A ρ hfin δ hδ E H
  let ZT := selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T
  let ZE := selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E
  have hRT : VolumeObjectGamma RT G := .of_term_context hc C hBase RT
  have hRE : VolumeObjectGamma RE G := .of_term_context hc C hBase RE
  have hZT : VolumeObjectGamma ZT G := selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin T
  have hZE : VolumeObjectGamma ZE G := selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E
  let iT := selectedVFTailVolumeIso hc C Ξ A ρ hfin δ hδ T F hFVF hFCon
  let iE := selectedVFTailVolumeIso hc C Ξ A ρ hfin δ hδ E H hHVF hHCon
  have hCT : CommonContextVolumeEquivalent G C ⟨RT,hRT⟩ ⟨ZT,hZT⟩ :=
    .of_iso iT (iT.gamma_of_term_context hc C hBase)
  have hCE : CommonContextVolumeEquivalent G C ⟨RE,hRE⟩ ⟨ZE,hZE⟩ :=
    .of_iso iE (iE.gamma_of_term_context hc C hBase)
  exact ((((hCT.symm hc).trans hc hNT).trans hc hCompare).trans hc (hNE.symm hc)).trans hc hCE

end IntegrationInACVF.Section7
