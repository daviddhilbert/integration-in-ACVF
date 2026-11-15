import Integration7.SmallDefinableClosures
import Integration7.GammaNamesGenericParameters
import IntegrationSection4.RVLabelSlices

/-! A genuine small context closed under definitions over the original
real/Gamma names and a finite RV parameter tuple. It contains the RV paradigms specified by a
cell while preserving all original independent VF tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaRVDefinableNamesVolumeContext (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk P.gamma < C.κ) {d : ℕ} (z : Fin d → CanonicalRV.RVSort M) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := definableClosureSubstructure hc (((C.base : Set M) ∪ commonRealNames P) ∪ Set.range (fun i => (z i).val))
  small := small_definable_closure hc C.uncountable _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le
      ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le C.small
        (commonRealNames_small C.uncountable.le P ((Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small) hΓ)))
      ((Set.finite_range (fun i => (z i).val)).lt_aleph0.trans_le C.uncountable.le)))
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,subset_definableClosure _ (Or.inl (Or.inl a.property))⟩,
      ⟨b.val,subset_definableClosure _ (Or.inl (Or.inl b.property))⟩,ha,hb,ha0,hb0,hab⟩

theorem gamma_rv_definable_names_context_contains
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (P : Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M)) (hΓ : Cardinal.mk P.gamma < C.κ) {d : ℕ} (z : Fin d → CanonicalRV.RVSort M) :
    ((C.base : Set M) ∪ commonRealNames P) ∪ Set.range (fun i => (z i).val) ⊆
      ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ z).base : Set M) := subset_definableClosure _

theorem gamma_rv_definable_names_context_singleton
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (P : Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M)) (hΓ : Cardinal.mk P.gamma < C.κ) {d : ℕ} (z : Fin d → CanonicalRV.RVSort M)
    {σ : SortTag} {x : M} (hx : DefinableAtBase (IntegrationInACVF.Section4.RVLabelSlices.labelBase P z) σ {x}) :
    x ∈ ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ z).base : Set M) := by
  apply (mem_definableClosure_iff_raw hc _ x).mpr
  apply hx.common_names.raw_definable.mono
  rintro y ((hy | hy) | hy)
  · exact Or.inl (Or.inl (hPC hy))
  · exact Or.inr hy
  · exact Or.inl (Or.inr (Or.inr hy))

private theorem independent_over_algebraic_subfield {K : Type} [Field K] {ι : Type}
    {E F : Subfield K} {x : ι → K}
    (hF : F ≤ (algebraicClosure E K).toSubfield) (hx : AlgebraicIndependent E x) :
    AlgebraicIndependent F x := by
  let A := (algebraicClosure E K).toSubfield
  letI := (Subfield.inclusion hF).toAlgebra
  letI : IsScalarTower F A K := .of_algebraMap_eq (fun _ => rfl)
  exact hx.algebraicClosure.restrictScalars
    (show Function.Injective (algebraMap F A) from fun _ _ he => Subtype.ext (congrArg (fun z : A => z.val) he))

theorem gamma_rv_definable_names_context_preserves_independence {n : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (P : Base (M := M))
    (hPC : P.real ⊆ (C.base : Set M)) (hΓ : Cardinal.mk P.gamma < C.κ) {d : ℕ} (z : Fin d → CanonicalRV.RVSort M) (hBase : P.real = (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField P.real) x) :
    AlgebraicIndependent (vfParameterField ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ z).base : Set M)) x := by
  let S := ((C.base : Set M) ∪ commonRealNames P) ∪ Set.range (fun i => (z i).val)
  have hField : vfParameterField S = vfParameterField P.real := by
    have hzRV : ∀ y ∈ Set.range (fun i => (z i).val), iRV y := by
      rintro y ⟨i,rfl⟩
      exact (z i).property
    change vfParameterField (((C.base : Set M) ∪ commonRealNames P) ∪ Set.range (fun i => (z i).val)) = _
    rw [vfParameterField_union_rv _ _ hzRV]
    change vfParameterField ((C.base : Set M) ∪ (P.real ∪ _)) = _
    rw [← hBase,← Set.union_assoc,Set.union_self]
    exact vfParameterField_union_rv _ _ (by rintro y ⟨δ,_,rfl⟩;exact (representative δ).val.property)
  apply independent_over_algebraic_subfield ?_ hx
  apply Subfield.closure_le.mpr
  intro y hy
  have hy' : y.val ∈ definableClosure S := hy
  obtain ⟨σ,hσ⟩ := definableClosure_subset_algebraicClosureSet S hy'
  have hv : AlgebraicAt S .vf y.val := by
    cases σ with
    | vf => exact hσ
    | rv =>
      have he := CanonicalStructure.sort_unique (inferInstance : M ⊨ Axioms.ACVF)
        (s := .vf) (t := .rv) y.property hσ.sorted
      cases he
  have ha := (algebraicAt_vf_iff_parameterField S y).mp hv
  rw [hField] at ha
  exact mem_algebraicClosure_iff.mpr ha

end IntegrationInACVF.Section7
