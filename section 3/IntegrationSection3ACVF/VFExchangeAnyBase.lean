import Section3.VFExchange

/-! Extends the pinned MIT Section3/VFExchange proof at revision
9cc9760892092dd34cfad4a6dee655843c52f30c to arbitrary real parameter sets.
The new field-closure identity removes its VFFieldBase hypothesis. -/

set_option backward.isDefEq.respectTransparency false

open Set FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open scoped IntermediateField.algebraAdjoinAdjoin

namespace IntegrationInACVF.Section3ACVF.VFExchangeAnyBase

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem parameterField_union_image (S : Set M) (X : Set (VFType (M := M))) :
    vfParameterField (S ∪ Subtype.val '' X) =
      (IntermediateField.adjoin (vfParameterField S) X).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield]
  have hr : Set.range (algebraMap (vfParameterField S) (VFType (M := M))) =
      (vfParameterField S : Set (VFType (M := M))) := by
    ext x
    exact ⟨fun ⟨a,ha⟩ => ha ▸ a.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have he : {x : VFType (M := M) | x.val ∈ S ∪ Subtype.val '' X} =
      {x : VFType (M := M) | x.val ∈ S} ∪ X := by
    ext x
    constructor
    · rintro (hx | ⟨y,hy,he⟩)
      · exact Or.inl hx
      · exact Or.inr ((Subtype.ext he : y = x) ▸ hy)
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨x,hx,rfl⟩
  change Subfield.closure {x : VFType (M := M) | x.val ∈ S ∪ Subtype.val '' X} = _
  rw [he,hr,Subfield.closure_union,Subfield.closure_union,Subfield.closure_eq]
  rfl

theorem algebraic_iff_matroid_closure (S : Set M) (X : Set (VFType (M := M)))
    (x : VFType (M := M)) :
    AlgebraicAt (S ∪ Subtype.val '' X) .vf x.val ↔
      x ∈ (AlgebraicIndependent.matroid (vfParameterField S) (VFType (M := M))).closure X := by
  rw [algebraicAt_vf_iff_parameterField,parameterField_union_image,
    AlgebraicIndependent.matroid_closure_eq]
  change IsAlgebraic (IntermediateField.adjoin (vfParameterField S) X) x ↔
    IsAlgebraic (Algebra.adjoin (vfParameterField S) X) x
  exact ⟨fun h => h.restrictScalars _,fun h => h.extendScalars
    (FaithfulSMul.algebraMap_injective (Algebra.adjoin (vfParameterField S) X)
      (IntermediateField.adjoin (vfParameterField S) X))⟩

theorem exchange (S : Set M) (a b : VFType (M := M))
    (hab : AlgebraicAt (insert b.val S) .vf a.val)
    (ha : ¬ AlgebraicAt S .vf a.val) : AlgebraicAt (insert a.val S) .vf b.val := by
  let N := AlgebraicIndependent.matroid (vfParameterField S) (VFType (M := M))
  have hab' : a ∈ N.closure {b} := (algebraic_iff_matroid_closure S {b} a).mp (by simpa using hab)
  have ha' : a ∉ N.closure ∅ := by
    intro h
    exact ha (by simpa using (algebraic_iff_matroid_closure S ∅ a).mpr h)
  have hb' := (N.closure_exchange (X := ∅) ⟨by simpa using hab',ha'⟩).1
  have h := (algebraic_iff_matroid_closure S {a} b).mpr (by simpa using hb')
  simpa using h

end IntegrationInACVF.Section3ACVF.VFExchangeAnyBase
