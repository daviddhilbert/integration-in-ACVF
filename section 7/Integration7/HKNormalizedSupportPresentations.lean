module

public import Integration7.HKNormalizedVolumeSupports

@[expose] public section

/-! The positive-generator support definition is exactly the span of
all actual corrected supported presentations, including degree zero.
Thus point normalization changes no supported generator scope. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedAllSupportedGenerators
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) : Set (NormalizedVolumeFunction hc C n) :=
  Set.range (fun f : SupportedGradedVolumeFunction hc C X =>
    normalizedVolumeFunctionGenerator hc C n (supportedGradedVolumeForgetAddHom hc C X f))

theorem normalized_volume_support_eq_span_all_supported
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    normalizedVolumeSupport hc C X =
      Submodule.span (NormalizedRVVolumeRing hc C) (normalizedAllSupportedGenerators hc C X) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨k,f,rfl⟩
    apply Submodule.subset_span
    refine ⟨DirectSum.of (SupportedVolumeFunctionComponent hc C X) (k+1) f,?_⟩
    exact congrArg (normalizedVolumeFunctionGenerator hc C n)
      (supported_graded_volume_forget_of hc C X (k+1) f)
  · apply Submodule.span_le.mpr
    rintro v ⟨f,rfl⟩
    exact normalized_supported_graded_generator_has_support hc C X f

end IntegrationInACVF.Section7.HK
