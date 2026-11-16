module

public import Integration7.NormalizedVolumePrefixOperators
public import Integration7.NormalizedVolumePermutationOperators
public import Integration7.NormalizedPositiveCoordinateFubini

@[expose] public section

/-! Every actual nonempty VF coordinate projection has an S-linear
partial integral on the full normalized function module, with the
genuine positive-generator pushforward formula and total Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedVolumeBaseDegreeEquiv {a b : ℕ} (h : a=b) :
    NormalizedVolumeFunction hc C b ≃ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C a := by
  cases h
  exact LinearEquiv.refl _ _

theorem normalized_volume_base_degree_positive {a b k : ℕ} (h : a=b) (f : AERVVolumeFunction hc C b k) :
    normalizedVolumeBaseDegreeEquiv hc C h (normalizedPositiveVolumeFunction hc C b k f) =
      normalizedPositiveVolumeFunction hc C a k (aeRVVolumeFunctionReindexBase hc C h f) := by
  cases h
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedVolumeCoordinatePushforward (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C p :=
  (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p).comp
    ((normalizedVolumePermuteBase hc C (p+E.discarded) (volumeProjectionFibreOrder E)).comp
      (normalizedVolumeBaseDegreeEquiv hc C (volume_projection_index_eq E)).toLinearMap)

theorem normalized_volume_coordinate_pushforward_positive (E : VFCoordinateProjection (n+1) (p+1))
    (k : ℕ) (f : AERVVolumeFunction hc C n k) :
    normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (normalizedPositiveVolumeFunction hc C n k f) =
    normalizedPositiveVolumeFunction hc C p (appendVolumeDegree E.discarded k)
      (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  change normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p
    (normalizedVolumePermuteBase hc C (p+E.discarded) (volumeProjectionFibreOrder E)
      (normalizedVolumeBaseDegreeEquiv hc C (volume_projection_index_eq E)
        (normalizedPositiveVolumeFunction hc C n k f))) = _
  rw [normalized_volume_base_degree_positive,normalized_volume_permute_base_positive,
    normalized_volume_prefix_integral_positive_value]
  rfl

theorem normalized_volume_coordinate_total_fubini (E : VFCoordinateProjection (n+1) (p+1)) :
    (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p).comp
      (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n := by
  apply normalized_volume_function_linearMap_ext_positive hc C n
  intro k f
  change normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
    (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (normalizedPositiveVolumeFunction hc C n k f)) = _
  rw [normalized_volume_coordinate_pushforward_positive]
  exact normalized_positive_coordinate_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f

theorem normalized_volume_coordinate_total_value (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) :
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f :=
  LinearMap.congr_fun (normalized_volume_coordinate_total_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E) f
end IntegrationInACVF.Section7
