module

public import Integration7.HKGradedAEVolumeFunctions
public import Integration7.HKSupportedZeroJacobianAddition
public import Integration7.SupportedVolumeJacobianAddition
public import Integration7.GradedSemiringActionLinearMaps

@[expose] public section

/-! Supported finite graded functions retain the actual weighted-zero
component. Their forgetful and Jacobian maps are assembled from the
actual homogeneous maps. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def SupportedVolumeFunctionComponent
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) : ℕ → Type
  | 0 => SupportedAEZeroVolumeFunction hc C X
  | k+1 => SupportedAERVVolumeFunction hc C X k

instance supportedVolumeFunctionComponentAddCommMonoid
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ) :
    AddCommMonoid (SupportedVolumeFunctionComponent hc C X j) := by
  cases j with
  | zero => exact supportedZeroVolumeFunctionAddCommMonoid hc C X
  | succ k => exact supportedVolumeFunctionAddCommMonoid hc C X

abbrev SupportedGradedVolumeFunction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  DirectSum ℕ (SupportedVolumeFunctionComponent hc C X)

def supportedVolumeComponentForgetAddHom
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ) :
    SupportedVolumeFunctionComponent hc C X j →+ AEVolumeFunctionComponent hc C n j := by
  cases j with
  | zero => exact supportedZeroVolumeFunctionForgetAddHom hc C X
  | succ k => exact supportedVolumeFunctionForgetAddHom hc C X

def supportedGradedVolumeForgetAddHom
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    SupportedGradedVolumeFunction hc C X →+ GradedAEVolumeFunction hc C n :=
  gradedComponentMapToSum (supportedVolumeComponentForgetAddHom hc C X)

theorem supported_graded_volume_forget_of
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedGradedVolumeForgetAddHom hc C X (DirectSum.of _ j f) =
      DirectSum.of _ j (supportedVolumeComponentForgetAddHom hc C X j f) :=
  graded_component_map_to_sum_of _ j f

def supportedVolumeComponentJacobianAddHom
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (j : ℕ) :
    SupportedVolumeFunctionComponent hc C X j →+ SupportedVolumeFunctionComponent hc C Y j := by
  cases j with
  | zero => exact supportedZeroVolumeJacobianAddHom hc C φ hφ
  | succ k => exact supportedVolumeJacobianAddHom hc C φ hφ

def supportedGradedVolumeJacobianAddHom
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedGradedVolumeFunction hc C X →+ SupportedGradedVolumeFunction hc C Y :=
  gradedComponentMapToSum (supportedVolumeComponentJacobianAddHom hc C φ hφ)

theorem supported_graded_volume_jacobian_of
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (j : ℕ)
    (f : SupportedVolumeFunctionComponent hc C X j) :
    supportedGradedVolumeJacobianAddHom hc C φ hφ (DirectSum.of _ j f) =
      DirectSum.of _ j (supportedVolumeComponentJacobianAddHom hc C φ hφ j f) :=
  graded_component_map_to_sum_of _ j f

end IntegrationInACVF.Section7.HK
