import Integration7.FrozenGenericCoefficientFields
import Integration7.SmallDefinableClosures
import IntegrationSection6.VFParameterCoefficientBases
import Integration7.GammaNamesGenericParameters

/-! Small containing contexts for the generated closure of a frozen
real/Gamma base. Only RV representatives are added to the frozen context
before definable closure, so the VF coefficient extension is algebraic. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def frozenGeneratedVolumeNames (C : BaseContext M) (B : Base (M := M))
    (x : Fin n → VF (M := M)) : Set M :=
  ((C.base : Set M) ∪ Set.range (fun j => (x j).val)) ∪
    (fun γ => raw (representative γ)) '' (vfParameterCoefficientBase B x).gamma

def frozenGeneratedVolumeContext (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (hBC : B.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (x : Fin n → VF (M := M)) : BaseContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  base := definableClosureSubstructure hc (frozenGeneratedVolumeNames C B x)
  small := small_definable_closure hc C.uncountable _
    ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt C.uncountable.le
      (small_union_range C.uncountable.le _ C.small _)
      (Cardinal.mk_image_le.trans_lt (vfParameterCoefficientBase_gamma_small C.uncountable
        ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hgamma x))))
  nontrivial_values := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    exact ⟨⟨a.val,subset_definableClosure _ (Or.inl (Or.inl a.property))⟩,
      ⟨b.val,subset_definableClosure _ (Or.inl (Or.inl b.property))⟩,ha,hb,ha0,hb0,hab⟩

theorem frozen_generated_context_contains (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (x : Fin n → VF (M := M)) :
    (C.base : Set M) ∪ Set.range (fun j => (x j).val) ⊆
      ((frozenGeneratedVolumeContext hc C B hBC hgamma x).base : Set M) :=
  fun _ h => subset_definableClosure _ (Or.inl h)

theorem frozen_generated_context_contains_names (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (x : Fin n → VF (M := M)) :
    commonRealNames (vfParameterCoefficientBase B x) ⊆
      ((frozenGeneratedVolumeContext hc C B hBC hgamma x).base : Set M) := by
  rintro y (hy | hy)
  · obtain ⟨σ,hy⟩ := hy
    apply (mem_definableClosure_iff_raw hc _ y).mpr
    apply hy.common_names.raw_definable.mono
    rintro z ((hz | hz) | hz)
    · exact Or.inl (Or.inl (hBC hz))
    · exact Or.inl (Or.inr hz)
    · exact Or.inl (Or.inl (hNames (Or.inr hz)))
  · exact subset_definableClosure _ (Or.inr hy)

private theorem independent_over_algebraic_subfield {K : Type} [Field K] {ι : Type}
    {E F : Subfield K} {z : ι → K}
    (hF : F ≤ (algebraicClosure E K).toSubfield) (hz : AlgebraicIndependent E z) :
    AlgebraicIndependent F z := by
  let A := (algebraicClosure E K).toSubfield
  letI := (Subfield.inclusion hF).toAlgebra
  letI : IsScalarTower F A K := .of_algebraMap_eq (fun _ => rfl)
  exact hz.algebraicClosure.restrictScalars
    (show Function.Injective (algebraMap F A) from fun _ _ he => Subtype.ext (congrArg (fun y : A => y.val) he))

theorem frozen_generated_context_preserves_independence {p : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hgamma : Cardinal.mk B.gamma < C.κ)
    (hGeneric : ∀ {q : ℕ} (y : Fin q → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x)
    (z : Fin p → VF (M := M))
    (hz : AlgebraicIndependent (vfParameterField (vfParameterCoefficientBase B x).real) z) :
    AlgebraicIndependent
      (vfParameterField ((frozenGeneratedVolumeContext hc C B hBC hgamma x).base : Set M)) z := by
  let R := (C.base : Set M) ∪ Set.range (fun j => (x j).val)
  have hzOriginal : AlgebraicIndependent
      (vfParameterField (B.real ∪ Set.range (fun j => (x j).val))) z := by
    apply independent_over_subfield
      (Subfield.closure_mono ?_) hz
    intro y hy
    exact (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1 hy
  have hzR : AlgebraicIndependent (vfParameterField R) z :=
    frozen_context_preserves_independence hGeneric x hx z hzOriginal
  have hField : vfParameterField (frozenGeneratedVolumeNames C B x) = vfParameterField R := by
    apply vfParameterField_union_rv
    rintro y ⟨γ,_,rfl⟩
    exact (representative γ).val.property
  apply independent_over_algebraic_subfield ?_ hzR
  apply Subfield.closure_le.mpr
  intro y hy
  have hy' : y.val ∈ definableClosure (frozenGeneratedVolumeNames C B x) := hy
  obtain ⟨σ,hσ⟩ := definableClosure_subset_algebraicClosureSet _ hy'
  have hv : AlgebraicAt (frozenGeneratedVolumeNames C B x) .vf y.val := by
    cases σ with
    | vf => exact hσ
    | rv =>
      have he := CanonicalStructure.sort_unique (inferInstance : M ⊨ Axioms.ACVF)
        (s := .vf) (t := .rv) y.property hσ.sorted
      cases he
  have ha := (algebraicAt_vf_iff_parameterField _ y).mp hv
  rw [hField] at ha
  exact mem_algebraicClosure_iff.mpr ha

end IntegrationInACVF.Section7
