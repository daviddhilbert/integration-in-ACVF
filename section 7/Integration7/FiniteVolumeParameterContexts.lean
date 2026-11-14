import Section3.ModelContext
import VFField
import Section4.SmallGeneratedBase

/-! Genuine small substructure contexts for finitely many named parameters.
These inherit the ambient model hypotheses, without asserting VF-field or
VF/Gamma generation for a term-generated substructure. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M]

def finiteVolumeParameterContext (C : BaseContext M) (F : Set M) (hF : F.Finite) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := Substructure.closure LRV ((C.base : Set M) ∪ F)
  small := small_generated_finite_extension C.uncountable C.base C.small F hF
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,Substructure.subset_closure (Or.inl a.property)⟩,
      ⟨b.val,Substructure.subset_closure (Or.inl b.property)⟩,ha,hb,ha0,hb0,hab⟩

theorem finiteVolumeParameterContext_contains (C : BaseContext M) (F : Set M) (hF : F.Finite) :
    (C.base : Set M) ∪ F ⊆ ((finiteVolumeParameterContext C F hF).base : Set M) :=
  Substructure.subset_closure

def vfParameterVolumeContext (C : BaseContext M) {n : ℕ} (x : Fin n → VFType (M := M)) : BaseContext M :=
  finiteVolumeParameterContext C (Set.range (fun i => (x i).val)) (Set.finite_range _)

theorem vfParameterVolumeContext_contains (C : BaseContext M) {n : ℕ}
    (x : Fin n → VFType (M := M)) :
    (C.base : Set M) ∪ Set.range (fun i => (x i).val) ⊆ ((vfParameterVolumeContext C x).base : Set M) :=
  finiteVolumeParameterContext_contains C _ _

end IntegrationInACVF.Section7
