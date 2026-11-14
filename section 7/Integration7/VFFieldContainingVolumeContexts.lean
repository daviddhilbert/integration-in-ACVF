import Integration7.FiniteVolumeParameterContexts
import IntegrationSection6.GammaFieldBaseReduction

/-! The generated VF coefficient field fits in a genuine small
containing context under the context's uncountable saturation bound. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def vfFieldContainingVolumeContext (C : BaseContext M) (P : Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M)) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := Substructure.closure LRV ((C.base : Set M) ∪ (vfFieldNamedBase P).real)
  small := small_generated_substructure C.uncountable _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le C.small
      (vfFieldNamedBase_small P C.uncountable ((Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small))))
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,Substructure.subset_closure (Or.inl a.property)⟩,
      ⟨b.val,Substructure.subset_closure (Or.inl b.property)⟩,ha,hb,ha0,hb0,hab⟩

theorem vfFieldContainingVolumeContext_contains (C : BaseContext M) (P : Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M)) :
    (C.base : Set M) ∪ (vfFieldNamedBase P).real ⊆
      ((vfFieldContainingVolumeContext C P hPC).base : Set M) := Substructure.subset_closure

end IntegrationInACVF.Section7
