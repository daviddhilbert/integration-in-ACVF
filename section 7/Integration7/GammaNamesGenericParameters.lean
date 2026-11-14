import Integration7.GammaNamesVolumeContexts
import Integration7.PreparedGenericRVCells
import Section3.AlgebraicClosure
import Section3.VFDefinableClosure
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! Naming representatives of the original Gamma parameters and taking
the real substructure closure preserves every original independent VF tuple.
Only an algebraic extension of the VF coefficient field is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

private theorem independent_over_algebraic_subfield {K : Type} [Field K] {ι : Type}
    {E F : Subfield K} {x : ι → K}
    (hF : F ≤ (algebraicClosure E K).toSubfield) (hx : AlgebraicIndependent E x) :
    AlgebraicIndependent F x := by
  let A := (algebraicClosure E K).toSubfield
  letI := (Subfield.inclusion hF).toAlgebra
  letI : IsScalarTower F A K := .of_algebraMap_eq (fun _ => rfl)
  have hi : Function.Injective (algebraMap F A) :=
    fun _ _ he => Subtype.ext (congrArg (fun z : A => z.val) he)
  exact hx.algebraicClosure.restrictScalars hi

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_names_context_preserves_independence {n : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (B : Base (M := M)) (hBC : B.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk B.gamma < C.κ) (hBase : B.real = (C.base : Set M))
    (x : Fin n → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x) :
    AlgebraicIndependent (vfParameterField ((gammaNamesContainingVolumeContext C B hBC hΓ).base : Set M)) x := by
  let S := (C.base : Set M) ∪ commonRealNames B
  have hField : vfParameterField S = vfParameterField B.real := by
    change vfParameterField ((C.base : Set M) ∪ (B.real ∪ _)) = _
    rw [← hBase,← Set.union_assoc,Set.union_self]
    exact vfParameterField_union_rv _ _ (by
      rintro z ⟨δ,_,rfl⟩
      exact (representative δ).val.property)
  have hClosure : Substructure.closure LRV S ≤ algebraicClosureSubstructure hc S :=
    Substructure.closure_le.mpr (subset_algebraicClosureSet S)
  apply independent_over_algebraic_subfield ?_ hx
  apply Subfield.closure_le.mpr
  intro y hy
  have hy' : y.val ∈ (Substructure.closure LRV S : Set M) := hy
  obtain ⟨σ,hσ⟩ := hClosure hy'
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
