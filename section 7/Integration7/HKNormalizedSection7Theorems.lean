import Integration7.HKNormalizedSupportedJacobians
import Integration7.NonemptyVolumeCoordinateProjections

/-! Corrected numbered normalized Fubini and change of variables on
actual supported normalized functions, with weighted-zero values retained
in the source module and no unproved cancellation or kernel premise. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_supported_two_projection_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E : VFCoordinateProjection (n+1) (p+1)) (F : VFCoordinateProjection (n+1) (q+1))
    (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)
      (normalizedSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f) =
      normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X F.retainedIndex)
        (normalizedSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X F f) :=
  (normalized_supported_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f).trans
    (normalized_supported_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X F f).symm

theorem theorem_7_14
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E F : Set (Fin (n+1))) (hE : E.Nonempty) (hF : F.Nonempty)
    (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (pureVFCoordinateImage X (nonemptyVolumeCoordinateProjection E hE).retainedIndex)
      (normalizedSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
        (nonemptyVolumeCoordinateProjection E hE) f) =
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (pureVFCoordinateImage X (nonemptyVolumeCoordinateProjection F hF).retainedIndex)
      (normalizedSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
        (nonemptyVolumeCoordinateProjection F hF) f) :=
  normalized_supported_two_projection_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X _ _ f

theorem theorem_7_15
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) (f : NormalizedSupportedVolumeFunction hc C X) :
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f =
      normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 Y
        (normalizedSupportedVolumeJacobian hc C φ hφ f) :=
  normalized_supported_volume_change_of_variables hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ f

end IntegrationInACVF.Section7.HK
