module

public import Integration7.RawPositiveCoordinateSupports
public import Integration7.PositiveGradedVolumeFubini
public import Integration7.SupportedPositiveGradedRestrictions

@[expose] public section

/-! Raw coordinate integration on the genuine supported positive graded
submodules, with literal projected support and its Fubini identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def rawPositiveVolumeSupportSubmodule
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Submodule (RVVolumeBlowupSemiring hc C) (PositiveGradedAEVolumeFunction hc C n) :=
  (supportedPositiveGradedForgetShift hc C X).range

theorem raw_positive_graded_generator_has_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : AERVVolumeFunction hc C n j) (hf : HasRawPositiveVolumeSupport hc C X f) :
    DirectSum.of (AERVVolumeFunction hc C n) j f ∈ rawPositiveVolumeSupportSubmodule hc C X := by
  obtain ⟨g,rfl⟩ := hf
  exact ⟨DirectSum.of (SupportedAERVVolumeFunction hc C X) j g,
    graded_component_map_to_sum_of (fun k => supportedVolumeFunctionForgetAddHom (k := k) hc C X) j g⟩

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_positive_graded_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : PositiveGradedAEVolumeFunction hc C n) (hf : f ∈ rawPositiveVolumeSupportSubmodule hc C X) :
    positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f ∈
      rawPositiveVolumeSupportSubmodule hc C (pureVFCoordinateImage X E.retainedIndex) := by
  obtain ⟨g,rfl⟩ := hf
  induction g using DirectSum.induction_on with
  | zero => simpa only [map_zero] using (rawPositiveVolumeSupportSubmodule hc C _).zero_mem
  | add f g hf hg =>
    simp only [map_add]
    exact (rawPositiveVolumeSupportSubmodule hc C _).add_mem hf hg
  | of j f =>
    change positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (gradedComponentMapToSum (fun k => supportedVolumeFunctionForgetAddHom (k := k) hc C X)
        (DirectSum.of _ j f)) ∈ _
    rw [graded_component_map_to_sum_of,positive_graded_signed_coordinate_of]
    exact raw_positive_graded_generator_has_support hc C _ _ _
      (raw_positive_signed_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E _ ⟨f,rfl⟩)

def rawPositiveSupportedCoordinateIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    rawPositiveVolumeSupportSubmodule hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      rawPositiveVolumeSupportSubmodule hc C (pureVFCoordinateImage X E.retainedIndex) :=
  LinearMap.codRestrict _
    ((positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).comp
      (rawPositiveVolumeSupportSubmodule hc C X).subtype)
    (fun f => raw_positive_graded_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f.val f.property)

def rawPositiveSupportedVolumeIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    rawPositiveVolumeSupportSubmodule hc C X →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C :=
  (positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (rawPositiveVolumeSupportSubmodule hc C X).subtype

theorem raw_positive_supported_coordinate_total_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    (rawPositiveSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)).comp
      (rawPositiveSupportedCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) =
      rawPositiveSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  exact positive_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f.val
end IntegrationInACVF.Section7
