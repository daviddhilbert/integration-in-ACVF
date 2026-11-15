import Integration7.NativeCoordinateVolumeFamilyRows
import Integration7.SelectedCoordinateVolumeRealizations
import Integration7.VolumeFamilyRealizationIdentifications

/-! Literal coordinate-density families may be integrated by any
specified standard contraction of their native source, without inserting
a further density graph into the contraction program. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem native_family_full_lift_realization_heq
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    HEq (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).fullLift
      (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ) := by
  let F := nativeCoordinateVolumeFamily hc A ρ hfin δ hδ
  let L := nativeSelectedRVVFTailLift hc A ρ
  let B := nativeProgramSelectedRVVFTailLift hc A ρ
  have hfinL := native_selected_rv_vf_tail_lift_finite_labels hc A ρ hfin
  have hfinB := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  let ω : VolumeForm (rawSpecialSet hc L) := F.fullLift.form
  let π : VolumeForm (rawSpecialSet hc B) := (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).form
  exact native_coordinate_volume_objects_heq hc (family_realization_degree_eq n k) L B rfl hfinL hfinB
    ω π δ (fun _ => rfl) (fun _ => rfl)

theorem native_coordinate_family_canonical_integral_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ) =
      positiveVolumeBlowupClass hc C (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T) := by
  have hClasses := dependent_degree_map_heq (fun j => positiveVFVolumeIsoClass hc C (k := j))
    (family_realization_degree_eq n k) (native_family_full_lift_realization_heq hc A ρ hfin δ hδ)
  have hIntegral := dependent_degree_map_heq
    (fun j => positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := j))
    (family_realization_degree_eq n k) hClasses
  exact (eq_of_heq ((selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ)).trans hIntegral)).trans
      (selected_coordinate_volume_realization_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 A ρ hfin δ hδ T)

end IntegrationInACVF.Section7
