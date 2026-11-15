import Integration7.PermutedRawContractionVolumeCharts
import Integration7.IntegrationCoordinateDensityFormula

/-! Actual coordinate-density VF objects have the expected covariance
under a VF coordinate permutation: their integral's RV volume tuple is
permuted by exactly the same finite permutation, with unchanged density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem native_vf_integral_permutation_covariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (σ : Equiv.Perm (Fin (n+1))) (ω : VolumeForm (rawSpecialSet hc A))
    (π : VolumeForm (rawSpecialSet hc (vfPermutationImage A σ))) (δ : Fin a)
    (hω : ∀ q, ω.value q=q.val.2 δ) (hπ : ∀ q, π.value q=q.val.2 δ)
    (T : StandardContraction A σ) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (nativeMixedVFVolumeObject hc (vfPermutationImage A σ)
        (vfPermutation_finite_rv_fibres A σ hfin) π)) =
      positiveVolumeClassPermute hc C σ
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
          (positiveVFVolumeIsoClass hc C (nativeMixedVFVolumeObject hc A hfin ω))) := by
  let hδ : ∀ q ∈ carrier A, (q.2 δ).val ≠ iRVZero := fun q hq =>
    (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨q,hq⟩ ((hω ⟨q,hq⟩).trans hz))
  have hU := positive_volume_integration_coordinate_density hc C Ξ hΞ hGenerated hNames γ hγ hγ1 A hfin ω δ hω T
  have hV := positive_volume_integration_coordinate_density hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (vfPermutationImage A σ) (vfPermutation_finite_rv_fibres A σ hfin) π δ hπ (identityContractionOnPermutedSource T)
  have hChart := positiveVolumeBlowupClass_iso hc C (permutedRawContractionVolumeIso hc C Ξ A hfin δ hδ T)
  exact hV.trans (hChart.symm.trans (congrArg (positiveVolumeClassPermute hc C σ) hU.symm))

end IntegrationInACVF.Section7
