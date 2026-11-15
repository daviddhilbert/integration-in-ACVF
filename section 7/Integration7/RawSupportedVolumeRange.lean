import Integration7.RawHomogeneousSupportAlgebra
import Integration7.GradedSemiringActionLifts
import Integration7.GradedComponentMapInjectivity

/-! The supported raw span is exactly the componentwise support space.
Actual supported components form a faithful graded module, giving both
directions without imposing a stronger definition of support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))

def rawVolumeComponentSupportAddSubmonoid (j : ℕ) : AddSubmonoid (AEVolumeFunctionComponent hc C n j) where
  carrier := {f | HasRawVolumeComponentSupport hc C X j f}
  zero_mem' := raw_volume_component_zero_has_support hc C X j
  add_mem' := fun hf hg => raw_volume_component_add_preserves_support hc C X j _ _ hf hg

abbrev RawSupportedVolumeComponent (j : ℕ) := ↥(rawVolumeComponentSupportAddSubmonoid hc C X j)

def rawSupportedComponentCoefficient (i j : ℕ) :
    RVVolumeBlowupClasses hc C i →+
      (rawVolumeComponentSupportAddSubmonoid hc C X j →+ rawVolumeComponentSupportAddSubmonoid hc C X (i+j)) where
  toFun u := {
    toFun := fun f => ⟨aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f.val,
      raw_volume_component_coefficient_preserves_support hc C X i j u f.val f.property⟩
    map_zero' := Subtype.ext ((aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u).map_zero)
    map_add' := fun f g => Subtype.ext ((aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u).map_add f.val g.val) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro f
    exact Subtype.ext (DFunLike.congr_fun (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j).map_zero f.val)
  map_add' u v := by
    apply AddMonoidHom.ext
    intro f
    exact Subtype.ext (DFunLike.congr_fun ((aeVolumeFunctionComponentCoefficientBiadditive hc C n i j).map_add u v) f.val)

def rawSupportedVolumeGradedAction :
    GradedSemiringAction (RVVolumeBlowupClasses hc C) (RawSupportedVolumeComponent hc C X) :=
  (aeVolumeFunctionGradedAction hc C n).lift
    (fun j => (rawVolumeComponentSupportAddSubmonoid hc C X j).subtype)
    (fun _ => Subtype.val_injective) (rawSupportedComponentCoefficient hc C X) (fun _ _ _ _ => rfl)

instance rawSupportedVolumeGradedModule :
    Module (RVVolumeBlowupSemiring hc C) (DirectSum ℕ (RawSupportedVolumeComponent hc C X)) :=
  gradedSemiringActionModule (rawSupportedVolumeGradedAction hc C X)

def rawSupportedVolumeComponentForget :
    DirectSum ℕ (RawSupportedVolumeComponent hc C X) →ₗ[RVVolumeBlowupSemiring hc C]
      GradedAEVolumeFunction hc C n :=
  gradedSemiringActionLinearMap (rawSupportedVolumeGradedAction hc C X) (aeVolumeFunctionGradedAction hc C n)
    (fun j => (rawVolumeComponentSupportAddSubmonoid hc C X j).subtype) (fun _ _ _ _ => rfl)

theorem raw_supported_volume_component_forget_of (j : ℕ)
    (f : rawVolumeComponentSupportAddSubmonoid hc C X j) :
    rawSupportedVolumeComponentForget hc C X (DirectSum.of _ j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) j f.val :=
  graded_component_map_to_sum_of (fun j => (rawVolumeComponentSupportAddSubmonoid hc C X j).subtype) j f

theorem raw_supported_volume_span_eq_range :
    rawSupportedVolumeSubmodule hc C X = (rawSupportedVolumeComponentForget hc C X).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro g ⟨j,f,hf,rfl⟩
    exact ⟨DirectSum.of _ j ⟨f,hf⟩,raw_supported_volume_component_forget_of hc C X j ⟨f,hf⟩⟩
  · rintro g ⟨f,rfl⟩
    induction f using DirectSum.induction_on with
    | zero => simpa only [map_zero] using (rawSupportedVolumeSubmodule hc C X).zero_mem
    | add f g hf hg =>
      rw [map_add]
      exact (rawSupportedVolumeSubmodule hc C X).add_mem hf hg
    | of j f =>
      rw [raw_supported_volume_component_forget_of]
      exact raw_supported_volume_generator_mem hc C X j f.val f.property

theorem raw_supported_volume_iff_componentwise (f : GradedAEVolumeFunction hc C n) :
    f ∈ rawSupportedVolumeSubmodule hc C X ↔ ∀ j, HasRawVolumeComponentSupport hc C X j (f j) := by
  constructor
  · rw [raw_supported_volume_span_eq_range]
    rintro ⟨g,rfl⟩ j
    have h := graded_component_map_to_sum_component
      (fun j => (rawVolumeComponentSupportAddSubmonoid hc C X j).subtype) g j
    exact h.symm ▸ (g j).property
  · intro hf
    rw [← DirectSum.sum_support_of f]
    apply (rawSupportedVolumeSubmodule hc C X).sum_mem
    intro j hj
    exact raw_supported_volume_generator_mem hc C X j (f j) (hf j)
end IntegrationInACVF.Section7
