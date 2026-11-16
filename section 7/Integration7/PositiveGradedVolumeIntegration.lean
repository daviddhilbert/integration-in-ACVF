module

public import Integration7.PositiveGradedDensityRescaling
public import Integration7.GradedAEVolumeIntegralLinearity
public import Integration7.GradedShiftComponents

@[expose] public section

/-! The positive raw graded module embeds in the full module, and its
integral is the restriction of the already checked full linear integral.
The displayed homogeneous formula uses the actual appended integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def positiveGradedAEVolumeInclusion (n : ℕ) :
    PositiveGradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      GradedAEVolumeFunction hc C n :=
  gradedShiftLinearEmbedding (aeVolumeFunctionGradedAction hc C n) 1

theorem positive_graded_ae_volume_inclusion_of (n j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumeInclusion hc C n (DirectSum.of _ j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1) f :=
  graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 j f

theorem positive_graded_ae_volume_inclusion_injective (n : ℕ) :
    Function.Injective (positiveGradedAEVolumeInclusion hc C n) :=
  graded_shift_to_sum_injective 1

def positiveGradedAEVolumePart (n : ℕ) :
    GradedAEVolumeFunction hc C n →+ PositiveGradedAEVolumeFunction hc C n :=
  DirectSum.toAddMonoid (fun j => match j with
    | 0 => 0
    | k+1 => DirectSum.of (AERVVolumeFunction hc C n) k)

theorem positive_graded_ae_volume_part_of (n j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumePart hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1) f) =
      DirectSum.of (AERVVolumeFunction hc C n) j f :=
  DirectSum.toAddMonoid_of (fun j => match j with
    | 0 => (0 : AEVolumeFunctionComponent hc C n 0 →+ PositiveGradedAEVolumeFunction hc C n)
    | k+1 => DirectSum.of (AERVVolumeFunction hc C n) k) (j+1) f

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def positiveGradedAEVolumeIntegral (n : ℕ) :
    PositiveGradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C :=
  (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (positiveGradedAEVolumeInclusion hc C n)

theorem positive_graded_ae_volume_integral_of (n j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (DirectSum.of _ j f) =
      DirectSum.of (RVVolumeBlowupClasses hc C) (appendVolumeDegree (n+1) j+1)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  change gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (positiveGradedAEVolumeInclusion hc C n (DirectSum.of _ j f)) = _
  rw [positive_graded_ae_volume_inclusion_of,graded_ae_volume_integral_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (by change n+(j+1)+1=appendVolumeDegree (n+1) j+1; rw [append_volume_degree_eq]; omega)
    (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))
end IntegrationInACVF.Section7
