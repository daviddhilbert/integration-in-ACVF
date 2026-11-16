module

public import Integration7.PositiveGradedScalarBalance
public import Integration7.NormalizedPositiveHeadGenerators

@[expose] public section

/-! The actual positive head integral extends to an S-linear operator
on the full normalized function module. Positive generators determine
it uniquely; degree-zero scalars are handled after point normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_positive_head_generator_scalar (n : ℕ)
    (r : RVVolumeBlowupSemiring hc C) (f : PositiveDegreeGradedVolumeFunction hc C (n+1)) :
    normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (r • f) =
      normalizedVolumeCoefficientMap hc C r •
        normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f :=
  graded_positive_scalar_balance (normalizedVolumeCoefficientMap hc C)
    (normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (rvVolumeBlowupClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))
    (normalized_volume_coefficient_point hc C)
    (normalized_positive_head_generator_positive_scalar hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n) r f

def normalizedPositiveDegreeHeadIntegral (n : ℕ) :
    NormalizedPositiveDegreeVolumeFunction hc C (n+1) →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  scalarExtensionLift (normalizedVolumeCoefficientMap hc C)
    (normalizedPositiveHeadGeneratorAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)
    (normalized_positive_head_generator_scalar hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n)

def normalizedVolumeHeadIntegral (n : ℕ) :
    NormalizedVolumeFunction hc C (n+1) →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (normalizedPositiveDegreeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (normalizedPositiveDegreeVolumeEquiv hc C (n+1)).symm.toLinearMap

set_option maxHeartbeats 1600000 in
theorem normalized_volume_head_integral_positive (n k : ℕ) (f : AERVVolumeFunction hc C (n+1) k) :
    normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (normalizedPositiveVolumeFunction hc C (n+1) k f) =
    normalizedPositiveVolumeFunction hc C n (k+1)
      (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  let g := DirectSum.of (fun j => AEVolumeFunctionComponent hc C (n+1) (j+1)) k f
  have hGen := normalized_positive_degree_equiv_generator hc C (n+1) g
  change normalizedPositiveDegreeVolumeEquiv hc C (n+1)
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g) = _ at hGen
  rw [show gradedShiftToSum (F := AEVolumeFunctionComponent hc C (n+1)) 1 g =
    DirectSum.of (AEVolumeFunctionComponent hc C (n+1)) (k+1) f from
      graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C (n+1)) 1 k f] at hGen
  change normalizedPositiveDegreeVolumeEquiv hc C (n+1)
    (scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _ g) =
      normalizedPositiveVolumeFunction hc C (n+1) k f at hGen
  change normalizedPositiveDegreeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    ((normalizedPositiveDegreeVolumeEquiv hc C (n+1)).symm (normalizedPositiveVolumeFunction hc C (n+1) k f)) = _
  rw [← hGen,LinearEquiv.symm_apply_apply]
  exact (scalar_extension_lift_generator _ _ _ g).trans
    (normalized_positive_head_generator_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f)

theorem normalized_volume_head_integral_unique (n : ℕ)
    (I : NormalizedVolumeFunction hc C (n+1) →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n)
    (hI : ∀ k (f : AERVVolumeFunction hc C (n+1) k),
      I (normalizedPositiveVolumeFunction hc C (n+1) k f) =
        normalizedPositiveVolumeFunction hc C n (k+1)
          (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)) :
    I=normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n :=
  normalized_volume_function_linearMap_ext_positive hc C (n+1)
    (fun k f => (hI k f).trans (normalized_volume_head_integral_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f).symm)
end IntegrationInACVF.Section7
