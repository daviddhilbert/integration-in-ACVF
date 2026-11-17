module

public import Integration7.HKSupportedJacobianCoefficientLaws
public import Integration7.HKGradedCoordinateIntegralLinearMaps
public import Integration7.HKSupportedGradedCoordinateFubini

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Full corrected raw supported function integration. The support
submodule is exactly the faithful image of actual supported graded
presentations. Coordinate integration and Jacobian maps are linear
and preserve the total integral on every function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawSupportedVolumeSubmodule
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Submodule (RVVolumeBlowupSemiring hc C) (GradedAEVolumeFunction hc C n) :=
  (supportedGradedVolumeForgetLinearMap hc C X).range

theorem raw_supported_volume_submodule_iff
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : GradedAEVolumeFunction hc C n) :
    f ∈ rawSupportedVolumeSubmodule hc C X ↔ f ∈ gradedVolumeSupport hc C X := Iff.rfl

def rawSupportedVolumeRangeEquiv
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedGradedVolumeFunction hc C X ≃ₗ[RVVolumeBlowupSemiring hc C] rawSupportedVolumeSubmodule hc C X :=
  LinearEquiv.ofInjective (supportedGradedVolumeForgetLinearMap hc C X)
    (supported_graded_volume_forget_injective hc C X)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def rawSupportedGradedVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C :=
  (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (supportedGradedVolumeForgetLinearMap hc C X)

def rawSupportedCoordinateRangeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    rawSupportedVolumeSubmodule hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      rawSupportedVolumeSubmodule hc C (pureVFCoordinateImage X E.retainedIndex) :=
  ((gradedAEVolumeCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).comp
    (rawSupportedVolumeSubmodule hc C X).subtype).codRestrict _ (by
      intro f
      change gradedAEVolumeCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f.val ∈ _
      rw [graded_ae_volume_coordinate_linear_value]
      exact graded_volume_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f.val f.property)

def rawSupportedCoordinateIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    SupportedGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      SupportedGradedVolumeFunction hc C (pureVFCoordinateImage X E.retainedIndex) :=
  (rawSupportedVolumeRangeEquiv hc C _).symm.toLinearMap.comp
    ((rawSupportedCoordinateRangeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E).comp
      (rawSupportedVolumeRangeEquiv hc C X).toLinearMap)

theorem raw_supported_coordinate_integral_forget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : SupportedGradedVolumeFunction hc C X) :
    supportedGradedVolumeForgetLinearMap hc C _ (rawSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f) =
      gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
        (supportedGradedVolumeForgetLinearMap hc C X f) := by
  have h := (rawSupportedVolumeRangeEquiv hc C (pureVFCoordinateImage X E.retainedIndex)).apply_symm_apply
    (rawSupportedCoordinateRangeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E (rawSupportedVolumeRangeEquiv hc C X f))
  exact (congrArg Subtype.val h).trans (graded_ae_volume_coordinate_linear_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E _)

theorem proposition_7_11
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)).comp
      (rawSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) =
      rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  change gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
    (supportedGradedVolumeForgetLinearMap hc C _ (rawSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f)) = _
  rw [raw_supported_coordinate_integral_forget]
  exact graded_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E _

theorem proposition_7_12
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (supportedGradedVolumeJacobianLinearMap hc C φ hφ) =
      rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun (raw_graded_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ) f

end IntegrationInACVF.Section7.HK
