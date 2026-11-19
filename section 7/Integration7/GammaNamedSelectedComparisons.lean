import Integration7.GammaNamedKernelObjects
import Integration7.SelectedSameOrderStandardVolumeComparison
import Integration7.SelectedFirstTwoStandardVolumeExchange
import Integration7.SelectedVolumeOrderIndependence
import Integration7.CanonicalSelectedTailVolumeCoordinates
import Integration7.NativeRawVolumeLabelMaps
import Integration7.GammaVolumeFullChartRestriction
import Integration7.GammaEssentialVolumeGraphs

/-! Gamma-named same-order and first-two comparisons of selected standard
contraction volume objects. The Gamma base `G` is arbitrary with real part
and common names in the code context `C`; the domain and contraction
programs carry Gamma certificates over `G`. The VF-tail completion charts
receive direct Gamma graphs instead of term-context certificates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d r : ℕ}

/-- The VF-tail completion chart has a full Gamma graph over `G`. -/
theorem selected_vf_tail_volume_iso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {s : Fin a → RV (M := M) | (x,s) ∈ carrier A ∧ s ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r}
    (E : OrderedContractionProgram (C.base : Set M) (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hE : GammaProgramDefinable G E)
    (hFull : GammaProgramDefinable G (selectedRVVFTailFullProgram hc T.program ρ E))
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1)
    (hCon : SpecialTransformations.Section5.Contractible E.toMap) :
    (selectedVFTailVolumeIso hc C G.gamma A ρ hfin δ hδ T E hVF hCon).GammaDefinable G := by
  have hfin' := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  have hδ' : ∀ p ∈ carrier (nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ),
      (p.2 δ).val ≠ iRVZero := fun p hp =>
    native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ (fun q => hδ q.val q.property) ⟨p,hp⟩
  have hW := raw_standard_volume_object_gamma hc C G hGC _
    (gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA) hfin' δ hδ'
    (selectedRVVFTailStandardContraction hc T ρ E) (gamma_selected_rv_vf_tail_standard_contraction hc T ρ E hFull)
  let f := canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E
  exact gamma_volume_iso_of_full_map _ (rawVolumeLabelMap hc f)
    (gamma_essential_volume_domain _ hW.coordinates)
    (raw_volume_label_map_gamma hc f
      (gamma_canonical_selected_tail_rv_projection hc T.target _ E (gamma_program_final_set E hE)))
    (fun _ => rfl)

/-- The VF-tail completion of a Gamma selected contraction is Gamma-named
common-context equivalent to the selected standard object. -/
theorem selected_tail_completion_common
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {s : Fin a → RV (M := M) | (x,s) ∈ carrier A ∧ s ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r}
    (E : OrderedContractionProgram (C.base : Set M) (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hE : GammaProgramDefinable G E)
    (hFull : GammaProgramDefinable G (selectedRVVFTailFullProgram hc T.program ρ E))
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1)
    (hCon : SpecialTransformations.Section5.Contractible E.toMap) :
    CommonContextVolumeEquivalent G C
      ⟨selectedTailCompletionVolumeObject hc C G.gamma A ρ hfin δ hδ T E,
        raw_standard_volume_object_gamma hc C G hGC _
          (gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA)
          (native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin) δ
          (fun p hp => native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ
            (fun q => hδ q.val q.property) ⟨p,hp⟩)
          (selectedRVVFTailStandardContraction hc T ρ E) (gamma_selected_rv_vf_tail_standard_contraction hc T ρ E hFull)⟩
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩ :=
  .of_iso (selectedVFTailVolumeIso hc C G.gamma A ρ hfin δ hδ T E hVF hCon)
    (selected_vf_tail_volume_iso_gamma hc C G hGC A hA ρ hfin δ hδ T E hE hFull hVF hCon)

set_option maxHeartbeats 3200000 in
theorem selected_same_order_standard_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T E : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E hE⟩ := by
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage A hA σ) hE ρ
  let A' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (d+n+1) a :=
    nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ
  let T' := selectedRVVFTailStandardContraction hc T ρ F
  let E' := selectedRVVFTailStandardContraction hc E ρ H
  have hA' : GammaSetDefinable G (carrier A') := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  have hT' := gamma_selected_rv_vf_tail_standard_contraction hc T ρ F hFullF
  have hE' := gamma_selected_rv_vf_tail_standard_contraction hc E ρ H hFullH
  have hfin' : ∀ x : Fin (d+n+1) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A'}.Finite :=
    native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  have hδ' : ∀ p ∈ carrier A', (p.2 δ).val ≠ iRVZero := fun p hp =>
    native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ (fun q => hδ q.val q.property) ⟨p,hp⟩
  have hCompare := retained_same_order_common_context hc C G hGC hΞ hGeneric γ hγ hγ1
    A' hA' hfin' δ hδ' T' E' hT' hE'
  have hNT := raw_standard_volume_normalization hc C G hGC A' hA' hfin' δ hδ' T' hT'
  have hNE := raw_standard_volume_normalization hc C G hGC A' hA' hfin' δ hδ' E' hE'
  have hCT := selected_tail_completion_common hc C G hGC A hA ρ hfin δ hδ T hT F hF hFullF hFVF hFCon
  have hCE := selected_tail_completion_common hc C G hGC A hA ρ hfin δ hδ E hE H hH hFullH hHVF hHCon
  exact ((((hCT.symm hc).trans hc hNT).trans hc hCompare).trans hc (hNE.symm hc)).trans hc hCE

set_option maxHeartbeats 3200000 in
theorem selected_first_two_standard_volume_exchange
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+2) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E hE⟩ := by
  obtain ⟨r,V,F,hF,hFVF,hFCon,hFullF⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  obtain ⟨s,W,H,hH,hHVF,hHCon,hFullH⟩ := selected_rv_vf_tail_full_program_exists hc E.program
    (gamma_vfPermutationImage A hA υ) hE ρ
  let A' : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (d+n+2) a :=
    nativeProgramSelectedRVVFTailLift (n := n+2) (d := d) hc A ρ
  let T' := selectedRVVFTailStandardContraction hc T ρ F
  let E' := selectedRVVFTailStandardContraction hc E ρ H
  have hA' : GammaSetDefinable G (carrier A') := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  have hT' := gamma_selected_rv_vf_tail_standard_contraction hc T ρ F hFullF
  have hE' := gamma_selected_rv_vf_tail_standard_contraction hc E ρ H hFullH
  have hfin' : ∀ x : Fin (d+n+2) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A'}.Finite :=
    native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  have hδ' : ∀ p ∈ carrier A', (p.2 δ).val ≠ iRVZero := fun p hp =>
    native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ (fun q => hδ q.val q.property) ⟨p,hp⟩
  obtain ⟨h0',h1',hTail'⟩ := selected_vf_tail_first_two_orders (d := d) σ υ h0 h1 hTail
  have hCompare := lemma_7_7_native hc C hGC hNames hΞ hGenerated γ hγ hγ1
    hGeneric A' hA' hfin' δ (fun p => hδ' p.val p.property) h0' h1' hTail' T' E' hT' hE'
  have hNT := raw_standard_volume_normalization hc C G hGC A' hA' hfin' δ hδ' T' hT'
  have hNE := raw_standard_volume_normalization hc C G hGC A' hA' hfin' δ hδ' E' hE'
  have hCT := selected_tail_completion_common hc C G hGC A hA ρ hfin δ hδ T hT F hF hFullF hFVF hFCon
  have hCE := selected_tail_completion_common hc C G hGC A hA ρ hfin δ hδ E hE H hH hFullH hHVF hHCon
  exact ((((hCT.symm hc).trans hc hNT).trans hc hCompare).trans hc (hNE.symm hc)).trans hc hCE

/-- The all-order comparison property for Gamma selected contraction volume objects. -/
def SelectedVolumeOrderIndependent (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (G : Base (M := M)) (n : ℕ) : Prop :=
  ∀ {a d : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin (n+1))) (T : StandardContraction A σ) (E : StandardContraction A υ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program),
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin E hE⟩

end IntegrationInACVF.Section7.GammaNamed
