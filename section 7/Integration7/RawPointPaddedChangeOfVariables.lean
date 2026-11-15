import Integration7.RawSection7FunctionTheorems
import Integration7.GradedPointPadding
import Integration7.CentralVolumePointClasses

/-! Raw change of variables after actual point padding, valid for all
ordinary and positive inputs. The point factor remains in the identity;
no unlocalized cancellation or altered RV[0] volume convention is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawAEVolumePointPadding (n : ℕ) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] PositiveGradedAEVolumeFunction hc C n :=
  gradedPointPaddingLinearMap (aeVolumeFunctionGradedAction hc C n)
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
    (volume_point_class_commutes hc C)

theorem raw_ae_volume_point_padding_of (j : ℕ) (f : AEVolumeFunctionComponent hc C n j) :
    rawAEVolumePointPadding hc C n (DirectSum.of _ j f) =
      DirectSum.of (AERVVolumeFunction hc C n) j
        (gradedDegreeAddEquiv (F := AEVolumeFunctionComponent hc C n) (Nat.add_comm 1 j)
          (aeVolumeFunctionComponentCoefficientBiadditive hc C n 1 j
            (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) f)) :=
  graded_component_map_to_sum_of _ j f

theorem raw_ae_volume_point_padding_inclusion (f : GradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeInclusion hc C n (rawAEVolumePointPadding hc C n f)=volumePointClass hc C • f :=
  graded_point_padding_embedding (aeVolumeFunctionGradedAction hc C n) _ f

theorem raw_point_padding_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (f : GradedAEVolumeFunction hc C n) (hf : f ∈ rawSupportedVolumeSubmodule hc C X) :
    rawAEVolumePointPadding hc C n f ∈ rawPositiveVolumeSupportSubmodule hc C X := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j,f,hf,rfl⟩ := hg
    rw [raw_ae_volume_point_padding_of]
    apply raw_positive_graded_generator_has_support hc C X j
    exact raw_volume_component_support_degree_heq hc C X (Nat.add_comm 1 j)
      (graded_degree_add_equiv_heq (Nat.add_comm 1 j) _).symm
      (raw_volume_component_coefficient_preserves_support hc C X 1 j _ f hf)
  | zero => simpa only [map_zero] using (rawPositiveVolumeSupportSubmodule hc C X).zero_mem
  | add f g hf hg ihf ihg =>
    rw [map_add]
    exact (rawPositiveVolumeSupportSubmodule hc C X).add_mem ihf ihg
  | smul r f hf ih =>
    rw [map_smul]
    exact (rawPositiveVolumeSupportSubmodule hc C X).smul_mem r ih

def rawSupportedVolumePointPadding
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    rawSupportedVolumeSubmodule hc C X →ₗ[RVVolumeBlowupSemiring hc C] SupportedPositiveGradedVolumeFunction hc C X :=
  (positiveGradedVolumeRestriction hc C X).comp
    ((rawAEVolumePointPadding hc C n).comp (rawSupportedVolumeSubmodule hc C X).subtype)

theorem raw_supported_volume_point_padding_forget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : rawSupportedVolumeSubmodule hc C X) :
    supportedPositiveGradedForgetShift hc C X (rawSupportedVolumePointPadding hc C X f)=
      rawAEVolumePointPadding hc C n f.val := by
  obtain ⟨g,hg⟩ := raw_point_padding_preserves_support hc C X f.val f.property
  change supportedPositiveGradedForgetShift hc C X
    (positiveGradedVolumeRestriction hc C X (rawAEVolumePointPadding hc C n f.val)) = _
  rw [← hg]
  exact congrArg (supportedPositiveGradedForgetShift hc C X)
    (LinearMap.congr_fun (positive_graded_volume_restriction_forget hc C X) g)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_supported_point_padding_integral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : rawSupportedVolumeSubmodule hc C X) :
    rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X (rawSupportedVolumePointPadding hc C X f)=
      volumePointClass hc C * rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f := by
  change positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (supportedPositiveGradedForgetShift hc C X (rawSupportedVolumePointPadding hc C X f)) = _
  rw [raw_supported_volume_point_padding_forget]
  change gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (positiveGradedAEVolumeInclusion hc C n (rawAEVolumePointPadding hc C n f.val)) = _
  rw [raw_ae_volume_point_padding_inclusion,map_smul]
  rfl

theorem raw_point_padded_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : rawSupportedVolumeSubmodule hc C X) :
    rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
      (supportedPositiveGradedJacobian hc C φ hφ (rawSupportedVolumePointPadding hc C X f)) =
      volumePointClass hc C * rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f :=
  (LinearMap.congr_fun (raw_positive_graded_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ)
    (rawSupportedVolumePointPadding hc C X f)).trans
      (raw_supported_point_padding_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f)
end IntegrationInACVF.Section7
