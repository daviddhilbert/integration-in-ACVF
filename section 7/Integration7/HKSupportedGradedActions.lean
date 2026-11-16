import Integration7.HKSupportedCoefficientProducts
import Integration7.HKUnivSupportedVolumeEquivalences
import Integration7.GradedSemiringActionLifts

/-! Literal supported functions carry the full corrected graded
coefficient action. The laws are transported through the faithful
forgetful maps, with the actual family products retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))

def supportedVolumeComponentWeightedCoefficient (j : ℕ) :
    RVBlowupClasses hc C 0 → SupportedVolumeFunctionComponent hc C X j → SupportedVolumeFunctionComponent hc C X j := by
  cases j with
  | zero => exact supportedZeroWeightedCoefficientProduct hc C X
  | succ k => exact supportedPositiveWeightedCoefficientProduct hc C X

theorem supported_volume_component_forget_weighted_coefficient (j : ℕ)
    (z : RVBlowupClasses hc C 0) (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedVolumeComponentForgetAddHom hc C X j (supportedVolumeComponentWeightedCoefficient hc C X j z f) =
      z • supportedVolumeComponentForgetAddHom hc C X j f := by
  cases j with
  | zero => exact supported_zero_forget_weighted_coefficient hc C X z f
  | succ k => exact supported_positive_forget_weighted_coefficient hc C X z f

def supportedVolumeComponentCoefficient (i j : ℕ) :
    RVBlowupClasses hc C i → SupportedVolumeFunctionComponent hc C X j → SupportedVolumeFunctionComponent hc C X (i+j) := by
  cases i with
  | zero =>
    exact fun z f => gradedDegreeAddEquiv (F := SupportedVolumeFunctionComponent hc C X) (Nat.zero_add j).symm
      (supportedVolumeComponentWeightedCoefficient hc C X j z f)
  | succ p =>
    cases j with
    | zero => exact supportedZeroPositiveCoefficientProduct hc C X
    | succ k => exact supportedPositiveVolumeCoefficientProduct hc C X

theorem supported_volume_component_forget_degree_heq {i j : ℕ} (h : i=j)
    (f : SupportedVolumeFunctionComponent hc C X i) :
    HEq (supportedVolumeComponentForgetAddHom hc C X j (gradedDegreeAddEquiv h f))
      (supportedVolumeComponentForgetAddHom hc C X i f) := by
  cases h
  rfl

theorem supported_volume_component_coefficient_forget (i j : ℕ)
    (u : RVBlowupClasses hc C i) (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedVolumeComponentForgetAddHom hc C X (i+j) (supportedVolumeComponentCoefficient hc C X i j u f) =
      aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u (supportedVolumeComponentForgetAddHom hc C X j f) := by
  cases i with
  | zero =>
    have hL := supported_volume_component_forget_degree_heq hc C X (Nat.zero_add j).symm
      (supportedVolumeComponentWeightedCoefficient hc C X j u f)
    rw [supported_volume_component_forget_weighted_coefficient] at hL
    exact eq_of_heq (hL.trans
      (ae_volume_component_zero_coefficient_heq hc C n j u (supportedVolumeComponentForgetAddHom hc C X j f)).symm)
  | succ p =>
    cases j with
    | zero => exact supported_zero_forget_positive_coefficient hc C X u f
    | succ k => exact supported_volume_forget_positive_coefficient hc C X u f

def supportedVolumeComponentCoefficientBiadditive (i j : ℕ) :
    RVBlowupClasses hc C i →+
      (SupportedVolumeFunctionComponent hc C X j →+ SupportedVolumeFunctionComponent hc C X (i+j)) where
  toFun u := {
    toFun := supportedVolumeComponentCoefficient hc C X i j u
    map_zero' := supported_volume_component_forget_injective hc C X (i+j) (by
      rw [supported_volume_component_coefficient_forget,map_zero,map_zero,map_zero])
    map_add' f g := supported_volume_component_forget_injective hc C X (i+j) (by
      simp only [supported_volume_component_coefficient_forget,map_add]) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro f
    apply supported_volume_component_forget_injective hc C X (i+j)
    change supportedVolumeComponentForgetAddHom hc C X (i+j) (supportedVolumeComponentCoefficient hc C X i j 0 f) =
      supportedVolumeComponentForgetAddHom hc C X (i+j) 0
    exact (supported_volume_component_coefficient_forget hc C X i j 0 f).trans
      ((DFunLike.congr_fun (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j).map_zero _).trans
        (map_zero (supportedVolumeComponentForgetAddHom hc C X (i+j))).symm)
  map_add' u v := by
    apply AddMonoidHom.ext
    intro f
    apply supported_volume_component_forget_injective hc C X (i+j)
    change supportedVolumeComponentForgetAddHom hc C X (i+j) (supportedVolumeComponentCoefficient hc C X i j (u+v) f) =
      supportedVolumeComponentForgetAddHom hc C X (i+j)
        (supportedVolumeComponentCoefficient hc C X i j u f + supportedVolumeComponentCoefficient hc C X i j v f)
    rw [map_add,supported_volume_component_coefficient_forget,supported_volume_component_coefficient_forget,
      supported_volume_component_coefficient_forget]
    exact DFunLike.congr_fun ((aeVolumeFunctionComponentCoefficientBiadditive hc C n i j).map_add u v) _

def supportedVolumeGradedAction : GradedSemiringAction (RVBlowupClasses hc C) (SupportedVolumeFunctionComponent hc C X) :=
  (aeVolumeFunctionGradedAction hc C n).lift (supportedVolumeComponentForgetAddHom hc C X)
    (supported_volume_component_forget_injective hc C X)
    (supportedVolumeComponentCoefficientBiadditive hc C X) (supported_volume_component_coefficient_forget hc C X)

instance supportedGradedVolumeFunctionModule :
    Module (RVVolumeBlowupSemiring hc C) (SupportedGradedVolumeFunction hc C X) :=
  gradedSemiringActionModule (supportedVolumeGradedAction hc C X)

def supportedGradedVolumeForgetLinearMap :
    SupportedGradedVolumeFunction hc C X →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (supportedVolumeGradedAction hc C X) (aeVolumeFunctionGradedAction hc C n)
    (supportedVolumeComponentForgetAddHom hc C X) (supported_volume_component_coefficient_forget hc C X)

end IntegrationInACVF.Section7.HK
