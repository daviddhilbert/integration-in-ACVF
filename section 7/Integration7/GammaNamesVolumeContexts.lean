module

public import Integration7.FiniteVolumeParameterContexts
public import Section3.GammaFullDescent

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! All original real and Gamma names fit in a genuine containing small
context. Actual maps may be realized there while retaining the original
mathematical Gamma base in their graph certificates. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaNamesContainingVolumeContext (C : BaseContext M) (B : Base (M := M))
    (hBC : B.real ⊆ (C.base : Set M)) (hΓ : Cardinal.mk B.gamma < C.κ) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := Substructure.closure LRV ((C.base : Set M) ∪ commonRealNames B)
  small := small_generated_substructure C.uncountable _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le C.small
      (commonRealNames_small C.uncountable.le B ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hΓ)))
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,Substructure.subset_closure (Or.inl a.property)⟩,
      ⟨b.val,Substructure.subset_closure (Or.inl b.property)⟩,ha,hb,ha0,hb0,hab⟩

theorem gamma_names_containing_volume_context_contains
    (C : BaseContext M) (B : Base (M := M)) (hBC : B.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk B.gamma < C.κ) :
    (C.base : Set M) ∪ commonRealNames B ⊆
      ((gammaNamesContainingVolumeContext C B hBC hΓ).base : Set M) := Substructure.subset_closure

end IntegrationInACVF.Section7
