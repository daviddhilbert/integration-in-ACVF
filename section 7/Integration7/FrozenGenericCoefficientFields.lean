module

public import Integration7.GenericCoordinateFibreDimension
public import Integration7.IndependentHeadCoordinateFields

@[expose] public section

/-! Independence can be passed to a frozen coefficient field before
and after the containing context is enlarged. All fields below are
actual generated subfields of the original VF field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7

theorem independent_append_over_tuple_field {K : Type} [Field K] {n p : ℕ}
    (E : Subfield K) (x : Fin n → K) (z : Fin p → K)
    (hx : AlgebraicIndependent E x) (hz : AlgebraicIndependent (tupleField E x) z) :
    AlgebraicIndependent E (Fin.append z x) := by
  rw [tupleField_eq_adjoin E x] at hz
  have h := hx.sumElim_of_tower (S := IntermediateField.adjoin E (Set.range x))
    (by rintro _ ⟨i,rfl⟩; exact ⟨⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩,rfl⟩) hz
  convert h.comp (finSumFinEquiv.symm : Fin (p+n) → Fin p ⊕ Fin n) finSumFinEquiv.symm.injective using 1
  funext i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin n ≃ Fin (p+n)).surjective i
  cases j <;> simp

theorem independent_prefix_over_tail_field {K : Type} [Field K] {n p : ℕ}
    (E : Subfield K) (x : Fin n → K) (z : Fin p → K)
    (h : AlgebraicIndependent E (Fin.append z x)) :
    AlgebraicIndependent (tupleField E x) z := by
  have hSum : AlgebraicIndependent E (Sum.elim z x) := by
    convert h.comp (finSumFinEquiv : Fin p ⊕ Fin n → Fin (p+n)) finSumFinEquiv.injective using 1
    funext i
    rcases i with i | i <;> simp
  rw [tupleField_eq_adjoin]
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    (AlgebraicIndependent.sumElim_iff.mp hSum).2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem frozen_context_preserves_independence {n p : ℕ} {R S : Set M}
    (hGeneric : ∀ {q : ℕ} (y : Fin q → VF (M := M)),
      AlgebraicIndependent (vfParameterField R) y → AlgebraicIndependent (vfParameterField S) y)
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField R) x)
    (z : Fin p → VF (M := M))
    (hz : AlgebraicIndependent (vfParameterField (R ∪ Set.range (fun i => (x i).val))) z) :
    AlgebraicIndependent (vfParameterField (S ∪ Set.range (fun i => (x i).val))) z := by
  have hR : vfParameterField (R ∪ Set.range (fun i => (x i).val)) =
      tupleField (vfParameterField R) x := vfParameterField_union_tuple R x
  have hS : vfParameterField (S ∪ Set.range (fun i => (x i).val)) =
      tupleField (vfParameterField S) x := vfParameterField_union_tuple S x
  have hz' := Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E z) hR) hz
  exact Eq.mpr (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E z) hS)
    (independent_prefix_over_tail_field _ x z
      (hGeneric _ (independent_append_over_tuple_field _ x z hx hz')))

theorem independent_over_subfield {K : Type} [Field K] {ι : Type}
    {E F : Subfield K} {z : ι → K} (hEF : E ≤ F) (hz : AlgebraicIndependent F z) :
    AlgebraicIndependent E z := by
  letI := (Subfield.inclusion hEF).toAlgebra
  letI : IsScalarTower E F K := .of_algebraMap_eq (fun _ => rfl)
  exact hz.restrictScalars
    (show Function.Injective (algebraMap E F) from fun _ _ he => Subtype.ext (congrArg (fun y : F => y.val) he))

end IntegrationInACVF.Section7
