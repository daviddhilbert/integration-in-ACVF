module

public import Integration7.NormalizedPositivePermutationGenerators
public import Integration7.PositiveGradedScalarBalance
public import Integration7.NormalizedHomogeneousIntegralValues

@[expose] public section

/-! Actual permutations of VF coordinates extend to S-linear maps on
the full normalized function module and preserve its total integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_positive_permutation_generator_scalar (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (r : RVVolumeBlowupSemiring hc C) (f : PositiveDegreeGradedVolumeFunction hc C n) :
    normalizedPositivePermutationGeneratorAddHom hc C n σ (r • f) =
      normalizedVolumeCoefficientMap hc C r • normalizedPositivePermutationGeneratorAddHom hc C n σ f :=
  graded_positive_scalar_balance (normalizedVolumeCoefficientMap hc C) (normalizedPositivePermutationGeneratorAddHom hc C n σ)
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
    (normalized_volume_coefficient_point hc C)
    (fun p u f => normalized_positive_permutation_generator_positive_scalar hc C n p σ u f) r f

def normalizedPositiveDegreePermutation (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    NormalizedPositiveDegreeVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  scalarExtensionLift (normalizedVolumeCoefficientMap hc C) (normalizedPositivePermutationGeneratorAddHom hc C n σ)
    (normalized_positive_permutation_generator_scalar hc C n σ)

def normalizedVolumePermuteBase (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (normalizedPositiveDegreePermutation hc C n σ).comp (normalizedPositiveDegreeVolumeEquiv hc C n).symm.toLinearMap

theorem normalized_volume_permute_base_positive (n k : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : AERVVolumeFunction hc C n k) :
    normalizedVolumePermuteBase hc C n σ (normalizedPositiveVolumeFunction hc C n k f) =
      normalizedPositiveVolumeFunction hc C n k (aeRVVolumeFunctionPermuteBase hc C σ f) := by
  change normalizedPositiveDegreePermutation hc C n σ
    ((normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n k f)) = _
  rw [normalized_positive_presentation_inverse]
  exact (scalar_extension_lift_generator _ _ _ _).trans
    (normalized_positive_permutation_generator_of hc C n k σ f)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_permute_base_total (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp (normalizedVolumePermuteBase hc C n σ) =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n := by
  apply normalized_volume_function_linearMap_ext_positive hc C n
  intro k f
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumePermuteBase hc C n σ (normalizedPositiveVolumeFunction hc C n k f)) = _
  rw [normalized_volume_permute_base_positive]
  exact normalized_positive_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f σ
end IntegrationInACVF.Section7
