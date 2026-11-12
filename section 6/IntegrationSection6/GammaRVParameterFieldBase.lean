import Section3.FieldBase
import IntegrationSection6.GammaWitnessUniformity

/-! Naming RV parameters preserves the field condition on the VF part of
an original real/Gamma base. This applies to every finite RV parameter
row without adding field-closure hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def VFFieldBase.unionRV {S R : Set M} (F : VFFieldBase S)
    (hR : ∀ r ∈ R, iRV r) : VFFieldBase (S ∪ R) where
  field := F.field
  mem_iff := by
    intro x
    rw [F.mem_iff]
    constructor
    · exact Or.inl
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · have he : SortTag.vf = SortTag.rv := CanonicalStructure.sort_unique hM x.property (hR x.val hx)
        cases he

noncomputable def VFFieldBase.withRVParameters {S : Set M} (F : VFFieldBase S)
    {p : ℕ} (z : Fin p → M) (hz : ∀ j, iRV (z j)) : VFFieldBase (S ∪ Set.range z) :=
  VFFieldBase.unionRV F (by rintro _ ⟨j,rfl⟩; exact hz j)

end IntegrationInACVF.Section6
