module

public import Integration7.NormalizedVolumeFunctions
public import Integration7.GradedAEVolumePrefixFubini

@[expose] public section

/-! The actual iterated prefix integral has the same normalized total
integral. This is a statement on the checked graded representatives;
no unproved linearity of the partial integral is assumed. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalized_volume_prefix_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (r n : ℕ) (f : GradedAEVolumeFunction hc C (n+r)) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedVolumeFunctionGenerator hc C n
        (gradedAEVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f)) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r)
      (normalizedVolumeFunctionGenerator hc C (n+r) f) := by
  rw [normalized_volume_integral_generator,normalized_volume_integral_generator]
  exact congrArg (normalizedVolumeCoefficientMap hc C)
    (graded_ae_volume_prefix_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f)

end IntegrationInACVF.Section7
