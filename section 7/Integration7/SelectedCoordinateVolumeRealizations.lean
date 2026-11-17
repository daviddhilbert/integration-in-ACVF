module

public import Integration7.IntegrationCoordinateDensityFormula
public import Integration7.SelectedVFTailVolumeCharts
public import Integration7.SelectedFamilyFullLifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An actual full VF realization of a retained-density RV family and
its integral computed by any specified selected standard contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

def selectedCoordinateVolumeRealization
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (d+n) := by
  let L := nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ
  have hL := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc L) δ
    (fun p => native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ
      (fun q => hδ q.val q.property) ⟨p.val,p.property⟩)
  exact nativeMixedVFVolumeObject hc L hL ω

theorem selected_coordinate_volume_realization_density
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (p : (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).domain) :
    (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).form.value p = p.val.2 δ := rfl

theorem selected_coordinate_volume_realization_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ)) =
      positiveVolumeBlowupClass hc C (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  obtain ⟨r,V,E,hE,hVF,hCon,hFull⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) (gamma_program_over_real_base G T.program) ρ
  let L := nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ
  have hL := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  let W := selectedCoordinateVolumeRealization hc A ρ hfin δ hδ
  have hIntegral := positive_volume_integration_coordinate_density hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    L hL W.form δ (fun _ => rfl) (selectedRVVFTailStandardContraction hc T ρ E)
  exact hIntegral.trans (positiveVolumeBlowupClass_iso hc C
    (selectedVFTailVolumeIso hc C Ξ A ρ hfin δ hδ T E hVF hCon))

end IntegrationInACVF.Section7
