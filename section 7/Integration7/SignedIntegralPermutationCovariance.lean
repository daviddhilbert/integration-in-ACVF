import Integration7.SignedCoordinateVolumeClasses
import Integration7.OrdinaryPermutationIntegralCovariance
import Integration7.VolumeFunctionIntegralPermutationCovariance

/-! The exact raw determinant correction restores total integrals
under VF order changes for both ordinary and positive family inputs.
No normalized point relation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_positive_volume_integral_signed_permutation
    (f : AERVVolumeFunction hc C n k) (σ : Equiv.Perm (Fin (n+1))) :
    signedVolumeClassPermutationCorrection (k := (k+1)+n) hc C
      (selectedVFTailPermutation (n := n+1) (k+1) σ)
      (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionPermuteBase hc C σ f)) =
      aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  rw [ae_rv_volume_function_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact signed_coordinate_volume_class_restore hc C _ _

theorem ae_ordinary_volume_integral_signed_permutation
    (f : AEOrdinaryRVVolumeFunction hc C n) (σ : Equiv.Perm (Fin (n+1))) :
    signedVolumeClassPermutationCorrection hc C σ
      (aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f)) =
      aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  rw [ae_ordinary_volume_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact signed_coordinate_volume_class_restore hc C _ _
end IntegrationInACVF.Section7
