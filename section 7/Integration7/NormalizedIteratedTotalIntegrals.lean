import Integration7.NormalizedPrefixFubini

/-! The actual prefix-then-total integral is balanced and additive
because of the proved geometric graded Fubini theorem. It therefore
extends to every element of the normalized scalar extension. This
constructs the iterated total functional, not a partial module map. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedIteratedTotalOnGenerators (r n : ℕ) :
    GradedAEVolumeFunction hc C (n+r) →+ NormalizedRVVolumeRing hc C where
  toFun f := normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeFunctionGenerator hc C n
      (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f))
  map_zero' := by rw [map_zero,map_zero,map_zero]
  map_add' f g := by
    rw [normalized_volume_prefix_fubini,normalized_volume_prefix_fubini,
      normalized_volume_prefix_fubini,map_add,map_add]

theorem normalized_iterated_total_generators_smul (r n : ℕ)
    (q : RVVolumeBlowupSemiring hc C) (f : GradedAEVolumeFunction hc C (n+r)) :
    normalizedIteratedTotalOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (q • f) =
      normalizedVolumeCoefficientMap hc C q •
        normalizedIteratedTotalOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f := by
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (normalizedVolumeFunctionGenerator hc C n
      (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n (q • f))) = _
  rw [normalized_volume_prefix_fubini]
  change _ = normalizedVolumeCoefficientMap hc C q •
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C n
        (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f))
  rw [normalized_volume_prefix_fubini,normalized_volume_function_generator_smul,map_smul]

def normalizedIteratedTotalIntegral (r n : ℕ) :
    NormalizedVolumeFunction hc C (n+r) →ₗ[NormalizedRVVolumeRing hc C] NormalizedRVVolumeRing hc C :=
  scalarExtensionLift (normalizedVolumeCoefficientMap hc C)
    (normalizedIteratedTotalOnGenerators hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)
    (normalized_iterated_total_generators_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n)

theorem normalized_iterated_total_integral_generator (r n : ℕ)
    (f : GradedAEVolumeFunction hc C (n+r)) :
    normalizedIteratedTotalIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
      (normalizedVolumeFunctionGenerator hc C (n+r) f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C n
        (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f)) :=
  scalar_extension_lift_generator _ _ _ f

theorem normalized_iterated_total_fubini (r n : ℕ) :
    normalizedIteratedTotalIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro f
  change normalizedIteratedTotalIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n
    (normalizedVolumeFunctionGenerator hc C (n+r) f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r)
      (normalizedVolumeFunctionGenerator hc C (n+r) f)
  rw [normalized_iterated_total_integral_generator]
  exact normalized_volume_prefix_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f

theorem normalized_iterated_total_integral_value (r n : ℕ)
    (f : NormalizedVolumeFunction hc C (n+r)) :
    normalizedIteratedTotalIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f =
      normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f :=
  LinearMap.congr_fun (normalized_iterated_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n) f

end IntegrationInACVF.Section7
