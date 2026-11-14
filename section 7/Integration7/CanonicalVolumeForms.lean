import Integration7.CanonicalVolumePresentations
import Integration7.RVNonzero

/-! Normalization transport of a density preserves its actual pointwise
value. In a canonical model no new parameters or points are introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def canonicalRawRVForm (hc : CanonicalStructure.IsCanonical (M := M))
    {A : @DefSet LRV M N (@rawRVSpace M N a) S}
    (ω : @VolumeForm M N hN _ S A) : VolumeForm (canonicalRawRVDomain hc A) := by
  let g := @VolumeForm.map M N hN _ S A ω
  refine ⟨canonicalRawRVMap hc g,?_⟩
  intro x
  apply (rv_nonzero_iff_raw _).2
  exact (@rv_nonzero_iff_raw M N hN ((g ⟨x.val,x.property⟩).val 0)).1
    (@VolumeForm.nonzero M N hN _ S A ω ⟨x.val,x.property⟩)

@[simp] theorem canonicalRawRVForm_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : @DefSet LRV M N (@rawRVSpace M N a) S}
    (ω : @VolumeForm M N hN _ S A) (x : canonicalRawRVDomain hc A) :
    (canonicalRawRVForm hc ω).value x =
      (@VolumeForm.map M N hN _ S A ω ⟨x.val,x.property⟩).val 0 := rfl

end IntegrationInACVF.Section7
