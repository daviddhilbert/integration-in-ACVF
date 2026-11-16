module

public import Integration7.NormalizedSupportedCoordinateIntegrals

@[expose] public section

/-! Partial integration on an arbitrary definable VF domain is a
linear operator on the full normalized function module. It agrees with
the geometric operator on source-supported functions, has the exact
projected support, and preserves their total integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedVolumeDomainCoordinatePushforward
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C p :=
  (normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X E.retainedIndex)).comp
    ((normalizedSupportedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E).comp
      (normalizedVolumeRestriction hc C X))

theorem normalized_volume_domain_coordinate_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex)
      (normalizedVolumeDomainCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f) :=
  normalized_supported_volume_has_support hc C _ _

theorem normalized_volume_domain_coordinate_agreement
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) (hf : HasNormalizedVolumeSupport hc C X f) :
    normalizedVolumeDomainCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f =
      normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f := by
  have h := LinearMap.congr_fun
    (normalized_supported_coordinate_pushforward_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E)
    (normalizedVolumeRestriction hc C X f)
  exact h.trans (congrArg (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E)
    ((normalized_volume_support_iff_projection hc C X f).mp hf))

theorem normalized_volume_domain_coordinate_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) (hf : HasNormalizedVolumeSupport hc C X f) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (normalizedVolumeDomainCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  rw [normalized_volume_domain_coordinate_agreement hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f hf]
  exact normalized_volume_coordinate_total_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f
end IntegrationInACVF.Section7
