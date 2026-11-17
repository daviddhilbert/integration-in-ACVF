module

public import Integration7.NormalizedVolumeCoefficientRing
public import Integration7.SemimoduleScalarExtension
public import Integration7.GradedAEVolumeIntegralLinearity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The normalized function module is the actual scalar extension of the
checked finite graded AE function semimodule. Its integral is obtained from
the checked graded integral by the universal property of this extension. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev NormalizedVolumeFunction (n : ℕ) :=
  SemimoduleScalarExtension (normalizedVolumeCoefficientMap hc C) (GradedAEVolumeFunction hc C n)

def normalizedVolumeFunctionGenerator (n : ℕ) :
    GradedAEVolumeFunction hc C n →+ NormalizedVolumeFunction hc C n :=
  scalarExtensionGeneratorHom (normalizedVolumeCoefficientMap hc C) _

theorem normalized_volume_function_generator_smul (n : ℕ)
    (r : RVVolumeBlowupSemiring hc C) (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumeFunctionGenerator hc C n (r • f) =
      normalizedVolumeCoefficientMap hc C r • normalizedVolumeFunctionGenerator hc C n f :=
  scalar_extension_generator_smul _ _ r f

theorem normalized_volume_function_point (n : ℕ) (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumeFunctionGenerator hc C n (volumePointClass hc C • f) =
      normalizedVolumeFunctionGenerator hc C n f := by
  rw [normalized_volume_function_generator_smul,normalized_volume_coefficient_point,one_smul]

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedVolumeIntegralOnGenerators (n : ℕ) :
    GradedAEVolumeFunction hc C n →+ NormalizedRVVolumeRing hc C :=
  (normalizedVolumeCoefficientMap hc C).toAddMonoidHom.comp
    (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).toAddMonoidHom

theorem normalized_volume_integral_generators_smul (n : ℕ)
    (r : RVVolumeBlowupSemiring hc C) (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumeIntegralOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (r • f) =
      normalizedVolumeCoefficientMap hc C r •
        normalizedVolumeIntegralOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  change normalizedVolumeCoefficientMap hc C
    (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (r • f)) = _
  rw [map_smul,smul_eq_mul,map_mul]
  rfl

def normalizedVolumeIntegral (n : ℕ) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedRVVolumeRing hc C :=
  scalarExtensionLift (normalizedVolumeCoefficientMap hc C)
    (normalizedVolumeIntegralOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (normalized_volume_integral_generators_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)

theorem normalized_volume_integral_generator (n : ℕ) (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C n f) =
    normalizedVolumeCoefficientMap hc C
      (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) :=
  scalar_extension_lift_generator _ _ _ f

theorem normalized_volume_integral_unique (n : ℕ)
    (I : NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedRVVolumeRing hc C)
    (hI : ∀ f, I (normalizedVolumeFunctionGenerator hc C n f) =
      normalizedVolumeCoefficientMap hc C
        (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f)) :
    I = normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n :=
  scalar_extension_lift_unique _ _ _ I hI

end IntegrationInACVF.Section7
