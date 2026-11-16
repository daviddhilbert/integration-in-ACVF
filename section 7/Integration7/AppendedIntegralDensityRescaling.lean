module

public import Integration7.SelectedFamilyDensityRescaleIntegrals
public import Integration7.DensityRescalingCoordinateCompatibility
public import Integration7.SignedIntegralPermutationCovariance
public import Integration7.SelectedPermutationSigns

@[expose] public section

/-! Raw density-rescaling and signed order identities in the appended
integral convention used by actual successive head operators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_rv_volume_appended_integral_density_rescale (f : AERVVolumeFunction hc C n k)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0) :
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionRescale hc C c hcS hc0 f)=
    positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  apply canonical_from_appended_injective hc C n k
  rw [ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1,
    canonical_from_appended_density_rescale,ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1,
    ae_rv_volume_integral_density_rescale hc C Ξ hΞ hGenerated hNames γ hγ hγ1]

theorem ae_rv_volume_appended_integral_signed_permutation (f : AERVVolumeFunction hc C n k)
    (σ : Equiv.Perm (Fin (n+1))) :
    positiveVolumeClassRescaleDefinable hc C (rvPermutationSign σ)⁻¹
      (Set.Definable.singleton_of_mem LRV (rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)))
      (inv_ne_zero (rvPermutationSign_ne_zero σ))
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionPermuteBase hc C σ f))=
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  apply canonical_from_appended_injective hc C n k
  rw [canonical_from_appended_density_rescale,
    ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1,
    ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  simpa only [signedVolumeClassPermutationCorrection,selected_vf_tail_rv_permutation_sign] using
    (ae_positive_volume_integral_signed_permutation hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f σ)
end IntegrationInACVF.Section7
