import Integration7.SmallDefinableClosures
import Section3.GammaBaseTools

/-! The code context of a Gamma-named base. Objects definable over the
Gamma-named base `⟨C.base, Ξ⟩` are coded over the definable closure of
`C.base` together with the proof-only common names of that base. This
context is only a code set: the Gamma-named categories built on it require
Gamma-definability over the original base `⟨C.base, Ξ⟩`, and no hypothesis
puts the common names into the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The Gamma-named base of a context: its real base and the Gamma points `Ξ`. -/
abbrev gammaNamedBase (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) : Base (M := M) :=
  ⟨(C.base : Set M),Ξ⟩

/-- The small code context: the definable closure of the original real base
together with the common names of the Gamma-named base. -/
def gammaNamedCodeContext (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := definableClosureSubstructure hc ((C.base : Set M) ∪ commonRealNames (gammaNamedBase C Ξ))
  small := small_definable_closure hc C.uncountable _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le C.small
      (commonRealNames_small C.uncountable.le _ C.small hΞ)))
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,subset_definableClosure _ (Or.inl a.property)⟩,
      ⟨b.val,subset_definableClosure _ (Or.inl b.property)⟩,ha,hb,ha0,hb0,hab⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

theorem gamma_named_code_context_base :
    (C.base : Set M) ⊆ ((gammaNamedCodeContext hc C Ξ hΞ).base : Set M) :=
  fun _ h => subset_definableClosure _ (Or.inl h)

theorem gamma_named_code_context_names :
    commonRealNames (gammaNamedBase C Ξ) ⊆ ((gammaNamedCodeContext hc C Ξ hΞ).base : Set M) :=
  fun _ h => subset_definableClosure _ (Or.inr h)

@[simp] theorem gamma_named_code_context_kappa : (gammaNamedCodeContext hc C Ξ hΞ).κ = C.κ := rfl

end IntegrationInACVF.Section7
