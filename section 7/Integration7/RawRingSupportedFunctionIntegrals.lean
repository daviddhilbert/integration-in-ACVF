module

public import Integration7.RawPointPaddedChangeOfVariables
public import Integration7.ScalarExtensionLinearFunctionals
public import Integration7.CentralVolumePointRing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The raw supported function modules with Grothendieck ring
coefficients, before point normalization. Fubini includes all ordinary
and positive generators and their formal differences. Positive change
of variables and the all-input point-padded identity extend linearly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev RawRingSupportedVolumeFunction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  SemimoduleScalarExtension (semiringGroupificationOf (RVVolumeBlowupSemiring hc C)) (rawSupportedVolumeSubmodule hc C X)

abbrev RawRingSupportedPositiveVolumeFunction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  SemimoduleScalarExtension (semiringGroupificationOf (RVVolumeBlowupSemiring hc C)) (SupportedPositiveGradedVolumeFunction hc C X)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def rawRingSupportedVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    RawRingSupportedVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C] RVVolumeBlowupRing hc C :=
  scalarExtensionFunctional (semiringGroupificationOf _)
    (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X)

def rawRingSupportedCoordinateIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    RawRingSupportedVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C]
      RawRingSupportedVolumeFunction hc C (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE)) :=
  scalarExtensionMap (semiringGroupificationOf _)
    (rawSupportedNonemptyCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE)

theorem proposition_7_11_ring
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    (rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE))).comp
      (rawRingSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE) =
      rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  unfold rawRingSupportedVolumeIntegral rawRingSupportedCoordinateIntegral
  rw [scalar_extension_functional_natural,proposition_7_11]

def rawRingSupportedPositiveVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    RawRingSupportedPositiveVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C] RVVolumeBlowupRing hc C :=
  scalarExtensionFunctional (semiringGroupificationOf _)
    (rawSupportedPositiveGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X)

omit Ξ hΞ hGenerated hNames γ hγ hγ1 in
def rawRingSupportedPositiveJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    RawRingSupportedPositiveVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C]
      RawRingSupportedPositiveVolumeFunction hc C Y :=
  scalarExtensionMap (semiringGroupificationOf _) (supportedPositiveGradedJacobian hc C φ hφ)

theorem proposition_7_12_positive_ring
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawRingSupportedPositiveVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (rawRingSupportedPositiveJacobian hc C φ hφ) =
      rawRingSupportedPositiveVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  unfold rawRingSupportedPositiveVolumeIntegral rawRingSupportedPositiveJacobian
  rw [scalar_extension_functional_natural,raw_positive_graded_change_of_variables]

omit Ξ hΞ hGenerated hNames γ hγ hγ1 in
def rawRingPointPaddedJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    RawRingSupportedVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C]
      RawRingSupportedPositiveVolumeFunction hc C Y :=
  scalarExtensionMap (semiringGroupificationOf _)
    ((supportedPositiveGradedJacobian hc C φ hφ).comp (rawSupportedVolumePointPadding hc C X))

theorem raw_ring_point_padded_change_of_variables
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : RawRingSupportedVolumeFunction hc C X) :
    rawRingSupportedPositiveVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
      (rawRingPointPaddedJacobian hc C φ hφ f) =
      volumePointRing hc C * rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f := by
  have hMaps : (rawRingSupportedPositiveVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (rawRingPointPaddedJacobian hc C φ hφ) =
      (LinearMap.mulRight (RVVolumeBlowupRing hc C) (volumePointRing hc C)).comp
        (rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X) := by
    apply scalar_extension_linearMap_ext (semiringGroupificationOf (RVVolumeBlowupSemiring hc C))
    intro g
    simp only [LinearMap.comp_apply,rawRingSupportedPositiveVolumeIntegral,rawRingPointPaddedJacobian,
      rawRingSupportedVolumeIntegral,scalar_extension_map_generator,scalar_extension_functional_generator,
      LinearMap.mulRight_apply]
    rw [raw_point_padded_change_of_variables,map_mul]
    exact (volume_point_ring_commutes hc C _).eq.symm
  exact (LinearMap.congr_fun hMaps f).trans (volume_point_ring_commutes hc C _).eq
end IntegrationInACVF.Section7
