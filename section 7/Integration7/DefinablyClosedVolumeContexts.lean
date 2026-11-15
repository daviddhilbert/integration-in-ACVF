import Integration7.SmallDefinableClosures
import Integration7.FiniteVolumeParameterContexts
import Section3.FieldBase

/-! A small containing volume context closed under actual definability.
Its VF part is a proved field, and every additional parameter is already
definable over the original context. No Gamma representative is added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def definablyClosedVolumeContext (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := definableClosureSubstructure hc (C.base : Set M)
  small := small_definable_closure hc C.uncountable _ C.small
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,subset_definableClosure _ a.property⟩,
      ⟨b.val,subset_definableClosure _ b.property⟩,ha,hb,ha0,hb0,hab⟩

theorem definably_closed_volume_context_contains
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (C.base : Set M) ⊆ ((definablyClosedVolumeContext hc C).base : Set M) :=
  subset_definableClosure _

theorem definably_closed_volume_context_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    ∀ d ∈ ((definablyClosedVolumeContext hc C).base : Set M), (C.base : Set M).Definable₁ LRV {d} :=
  fun d hd => (mem_definableClosure_iff_raw hc _ d).mp hd

def definablyClosedVolumeContextField
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    VFFieldBase ((definablyClosedVolumeContext hc C).base : Set M) where
  field := vfDefinableClosureField (C.base : Set M)
  mem_iff x := by
    constructor
    · intro hx
      exact ⟨.vf,hx⟩
    · rintro ⟨σ,hx⟩
      have he : σ = .vf := CanonicalStructure.sort_unique (M := M) inferInstance
        (hx.2 (Set.mem_singleton _)) x.property
      cases he
      exact hx

end IntegrationInACVF.Section7
