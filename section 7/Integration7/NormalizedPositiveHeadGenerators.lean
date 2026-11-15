import Integration7.NormalizedPositiveCoefficientActions
import Integration7.NormalizedPositiveDegreeFunctions
import Integration7.AERVVolumeHeadIntegralPositiveCoefficients

/-! An actual additive head integral on positive graded generators,
with normalized compatibility for every positive homogeneous scalar. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
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

def normalizedPositiveHeadGeneratorAddHom (n : ℕ) :
    PositiveDegreeGradedVolumeFunction hc C (n+1) →+ NormalizedVolumeFunction hc C n :=
  DirectSum.toAddMonoid (fun k => (normalizedVolumeFunctionGenerator hc C n).comp
    ((DirectSum.of (AEVolumeFunctionComponent hc C n) ((k+1)+1)).comp
      (aeRVVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k)))

theorem normalized_positive_head_generator_of (n k : ℕ) (f : AERVVolumeFunction hc C (n+1) k) :
    normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (fun j => AEVolumeFunctionComponent hc C (n+1) (j+1)) k f) =
    normalizedPositiveVolumeFunction hc C n (k+1)
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) :=
  DirectSum.toAddMonoid_of _ k f

theorem normalized_positive_head_generator_positive_scalar (n p : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : PositiveDegreeGradedVolumeFunction hc C (n+1)) :
    normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u • f) =
    normalizedVolumeCoefficientMap hc C (DirectSum.of (RVVolumeBlowupClasses hc C) (p+1) u) •
      normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  induction f using DirectSum.induction_on with
  | zero => rw [smul_zero,map_zero,smul_zero]
  | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
  | of k f =>
    rw [graded_semiring_action_of_of ((aeVolumeFunctionGradedAction hc C (n+1)).shift 1),
      normalized_positive_head_generator_of,normalized_positive_head_generator_of]
    change normalizedPositiveVolumeFunction hc C n (((p+1)+k)+1)
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionPositiveCoefficientProduct hc C (n+1) p k u f)) = _
    rw [ae_rv_volume_head_integral_positive_coefficient]
    exact normalized_positive_function_coefficient hc C n p (k+1) u _
end IntegrationInACVF.Section7
