module

public import Integration7.SupportedVolumeHeadIntegrals
public import Integration7.NormalizedVolumeHeadOperators
public import Integration7.NormalizedVolumeSupports

@[expose] public section

/-! Actual normalized head pushforward between the supported function
modules of a domain and its VF projection. The target restriction is
proved to preserve the unmodified geometric head integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedSupportedHeadIntegral
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C (pureVFCoordinateImage X Fin.succ) :=
  (normalizedVolumeRestriction hc C (pureVFCoordinateImage X Fin.succ)).comp
    ((normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
      (normalizedSupportedVolumeForget hc C X))

theorem normalized_supported_head_integral_positive
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) (k : ℕ)
    (f : SupportedAERVVolumeFunction hc C X k) :
    normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
      (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f)) =
    normalizedSupportedVolumeGenerator hc C (pureVFCoordinateImage X Fin.succ)
      (DirectSum.of (SupportedAERVVolumeFunction hc C (pureVFCoordinateImage X Fin.succ)) (k+1)
        (supportedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f)) := by
  change normalizedVolumeRestriction hc C (pureVFCoordinateImage X Fin.succ)
    (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedSupportedVolumeForget hc C X
        (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f)))) = _
  rw [normalized_supported_volume_forget_generator,normalized_volume_head_integral_positive,
    ← supported_volume_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f,
    normalized_volume_restriction_positive,ae_volume_restriction_forget_supported]

theorem normalized_supported_head_integral_forget
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) :
    (normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X Fin.succ)).comp
      (normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X) =
    (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
      (normalizedSupportedVolumeForget hc C X) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro g
  change normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X Fin.succ)
    (normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
      (normalizedSupportedVolumeGenerator hc C X g)) =
    normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedSupportedVolumeForget hc C X (normalizedSupportedVolumeGenerator hc C X g))
  induction g using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of k f =>
    change normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X Fin.succ)
      (normalizedSupportedHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
        (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f))) =
      normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (normalizedSupportedVolumeForget hc C X
          (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f)))
    rw [normalized_supported_head_integral_positive,normalized_supported_volume_forget_generator,
      normalized_supported_volume_forget_generator,normalized_volume_head_integral_positive,
      supported_volume_head_integral_forget]
end IntegrationInACVF.Section7
