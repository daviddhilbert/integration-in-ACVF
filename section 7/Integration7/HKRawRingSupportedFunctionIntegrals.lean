module

public import Integration7.HKRawSupportedFunctionLinearIntegrals
public import Integration7.HKRawVolumeKernelIdeal
public import Integration7.ScalarExtensionLinearFunctionals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Balanced scalar extension gives the unnormalized supported function
modules over the corrected Grothendieck coefficient ring. Actual
coordinate and Jacobian maps extend linearly, and Fubini and change
of variables hold on every function and formal difference. -/
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

abbrev RawRingSupportedVolumeFunction
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :=
  SemimoduleScalarExtension (semiringGroupificationOf (RVVolumeBlowupSemiring hc C))
    (SupportedGradedVolumeFunction hc C X)

def rawRingSupportedJacobian
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    RawRingSupportedVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C] RawRingSupportedVolumeFunction hc C Y :=
  scalarExtensionMap (semiringGroupificationOf _) (supportedGradedVolumeJacobianLinearMap hc C φ hφ)

theorem raw_ring_supported_jacobian_generator
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ)
    (f : SupportedGradedVolumeFunction hc C X) :
    rawRingSupportedJacobian hc C φ hφ (scalarExtensionGeneratorHom (semiringGroupificationOf _) _ f) =
      scalarExtensionGeneratorHom (semiringGroupificationOf _) _ (supportedGradedVolumeJacobianLinearMap hc C φ hφ f) :=
  scalar_extension_map_generator _ _ f

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
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    RawRingSupportedVolumeFunction hc C X →ₗ[RVVolumeBlowupRing hc C]
      RawRingSupportedVolumeFunction hc C (pureVFCoordinateImage X E.retainedIndex) :=
  scalarExtensionMap (semiringGroupificationOf _)
    (rawSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E)

theorem proposition_7_11_ring
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    (rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)).comp
      (rawRingSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) =
      rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  unfold rawRingSupportedVolumeIntegral rawRingSupportedCoordinateIntegral
  rw [scalar_extension_functional_natural,proposition_7_11]

theorem proposition_7_12_ring
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)} (φ : Map X Y) (hφ : Function.Bijective φ) :
    (rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y).comp
      (rawRingSupportedJacobian hc C φ hφ) =
      rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  unfold rawRingSupportedVolumeIntegral rawRingSupportedJacobian
  rw [scalar_extension_functional_natural,proposition_7_12]

theorem raw_ring_supported_integral_generator
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : SupportedGradedVolumeFunction hc C X) :
    rawRingSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
        (scalarExtensionGeneratorHom (semiringGroupificationOf _) _ f) =
      semiringGroupificationOf (RVVolumeBlowupSemiring hc C)
        (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f) :=
  scalar_extension_functional_generator _ _ f

end IntegrationInACVF.Section7.HK
