import Integration7.VFVolumeIntegralPermutationCovariance
import Integration7.VFVolumeDegreeReindexing
import Integration7.VolumeFunctionIntegralCoordinateNormalization

/-! The genuine coefficient-first VF realization of a selected volume
family. It puts the selected RV realizations before the original VF base
and integrates to the actual appended family integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

theorem appended_family_lift_degree_eq (n k : ℕ) : appendVolumeDegree n k=n+k := by
  rw [append_volume_degree_eq]
  omega

def SelectedVFVolumeFamily.appendedFullLift (F : SelectedVFVolumeFamily C n a k) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree n k) :=
  (F.fullLift.reindexDegree (appended_family_lift_degree_eq n k)).permuteVF
    (appendedToOriginalVolumePermutation n k).symm

theorem selected_family_appended_integral_full_lift
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C F.appendedFullLift) = selectedFamilyIntegralValue hc C Ξ hGenerated F := by
  let e := appendedToOriginalVolumePermutation (n+1) k
  let U := F.fullLift.reindexDegree (appended_family_lift_degree_eq (n+1) k)
  have hReindex := positive_vf_volume_integration_reindex_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    F.fullLift (appended_family_lift_degree_eq (n+1) k)
  have hCanonical := selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
  have hDegree := positive_volume_class_reindex_degree_heq hc C (selected_append_degree_eq n k)
    (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F)
  have hU : positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C U) = positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k)
        (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F) :=
    eq_of_heq (hReindex.trans (hCanonical.symm.trans hDegree.symm))
  have hCov := positive_vf_volume_integral_permutation_covariance hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U e.symm
  rw [hU,← selected_family_appended_canonical_coordinate_formula hc C Ξ hGenerated F] at hCov
  have hCancel : positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C e.symm
      (positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C e
        (selectedFamilyIntegralValue hc C Ξ hGenerated F)) = selectedFamilyIntegralValue hc C Ξ hGenerated F := by
    generalize selectedFamilyIntegralValue hc C Ξ hGenerated F = z
    induction z using Quotient.inductionOn with
    | h V => exact positiveVolumeBlowupClass_iso hc C (volumePermutationCancelIso hc C V e)
  exact hCov.trans hCancel

end IntegrationInACVF.Section7
