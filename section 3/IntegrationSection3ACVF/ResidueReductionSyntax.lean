import IntegrationSection3ACVF.BallResidueChart

/-! A full LRV graph for the actual valuation-ring residue map. Its
quantifier-free formula uses the existing RV zero and preorder. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity

noncomputable section

namespace IntegrationInACVF.Section3ACVF.ResidueReductionSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawGraph : Set (Fin 2 → M) := {z | iVF (z 0) ∧ iLe iRVOne (iRv (z 0)) ∧
  ((iLe (iRv (z 0)) iRVOne ∧ z 1 = iRv (z 0)) ∨
    (¬ iLe (iRv (z 0)) iRVOne ∧ z 1 = iRVZero))}

def formula (S : Set M) : LRV.Formula (S ⊕ Fin 2) :=
  let x : LRV.Term ((S ⊕ Fin 2) ⊕ Fin 0) := .var (.inl (.inr 0))
  let y : LRV.Term ((S ⊕ Fin 2) ⊕ Fin 0) := .var (.inl (.inr 1))
  let rvx : LRV.Term ((S ⊕ Fin 2) ⊕ Fin 0) := .func Fn.rvMap ![x]
  let one : LRV.Term ((S ⊕ Fin 2) ⊕ Fin 0) := .func Fn.rvOne Fin.elim0
  let zero : LRV.Term ((S ⊕ Fin 2) ⊕ Fin 0) := .func Fn.rvZero Fin.elim0
  (BoundedFormula.rel Rel.memVF ![x]) ⊓ ((BoundedFormula.rel Rel.rvLe ![one,rvx]) ⊓
    (((BoundedFormula.rel Rel.rvLe ![rvx,one]) ⊓ (BoundedFormula.equal y rvx)) ⊔
      ((∼(BoundedFormula.rel Rel.rvLe ![rvx,one])) ⊓ (BoundedFormula.equal y zero))))

private theorem eval_one {α : Type} (w : α → M) (a : LRV.Term α) :
    (fun i => (![a] i).realize w) = ![a.realize w] := by
  funext i
  fin_cases i
  rfl

private theorem eval_two {α : Type} (w : α → M) (a b : LRV.Term α) :
    (fun i => (![a,b] i).realize w) = ![a.realize w,b.realize w] := by
  funext i
  fin_cases i <;> rfl

private theorem eval_zero {α : Type} (w : α → M) :
    (fun i : Fin 0 => (Fin.elim0 i : LRV.Term α).realize w) = Fin.elim0 := by
  funext i
  exact i.elim0

theorem formula_realize (S : Set M) (z : Fin 2 → M) :
    (formula S).Realize (Sum.elim Subtype.val z) ↔ z ∈ rawGraph (M := M) := by
  simp only [formula,Formula.Realize,BoundedFormula.realize_inf,BoundedFormula.realize_sup,
    BoundedFormula.realize_not,BoundedFormula.Realize,eval_one,eval_two,eval_zero,Term.realize,Function.comp_def,
    Matrix.cons_val_zero,Matrix.cons_val_one,Sum.elim_inl,Sum.elim_inr]
  rfl

theorem rawGraph_definable (S : Set M) : S.Definable LRV (rawGraph (M := M)) := by
  apply Set.definable_iff_exists_formula_sum.mpr
  exact ⟨formula S,Set.ext fun z => (formula_realize S z).symm⟩

theorem residue_iff (u : Values.presentationValuation.valuationSubring) (t : M) :
    (![u.val.val,t] : Fin 2 → M) ∈ rawGraph (M := M) ↔
      t = (residueRV (IsLocalRing.residue Values.presentationValuation.valuationSubring u)).val := by
  let v := Values.presentationValuation (M := M)
  have hlo : iLe iRVOne (iRv u.val.val) := by
    have h := (Values.presentation_compatible u.val 1).mpr
      (show v u.val ≤ v 1 from (map_one v).symm ▸ (Valuation.mem_valuationSubring_iff v _).mp u.property)
    change iLe (iRv (1 : VFType (M := M)).val) (iRv u.val.val) at h
    change iLe (iRv iVFOne) (iRv u.val.val) at h
    rwa [RVCalc.rv_one hM] at h
  have hhi : iLe (iRv u.val.val) iRVOne ↔ v u.val = 1 := by
    have h := Values.presentation_compatible (1 : VFType (M := M)) u.val
    change iLe (iRv u.val.val) (iRv (1 : VFType (M := M)).val) ↔ v 1 ≤ v u.val at h
    change iLe (iRv u.val.val) (iRv iVFOne) ↔ v 1 ≤ v u.val at h
    rw [RVCalc.rv_one hM,map_one] at h
    exact h.trans ⟨fun hu => le_antisymm ((Valuation.mem_valuationSubring_iff v _).mp u.property) hu,
      fun hu => hu.ge⟩
  have he := CanonicalResidue.toRV_residue v Values.presentation_compatible u
  change CanonicalResidue.toRV v Values.presentation_compatible (IsLocalRing.residue v.valuationSubring u) = _ at he
  change (iVF u.val.val ∧ iLe iRVOne (iRv u.val.val) ∧
    ((iLe (iRv u.val.val) iRVOne ∧ t = iRv u.val.val) ∨
      (¬ iLe (iRv u.val.val) iRVOne ∧ t = iRVZero))) ↔ _
  rw [and_iff_right u.val.property,and_iff_right hlo,hhi]
  change _ ↔ t = (CanonicalResidue.toRV v Values.presentation_compatible (IsLocalRing.residue v.valuationSubring u)).val
  rw [he]
  by_cases hu : v u.val = 1
  · simp only [hu,true_and,not_true_eq_false,false_and,or_false,CanonicalResidue.reduction,if_pos hu]
    rfl
  · simp only [hu,false_and,not_false_eq_true,true_and,false_or,CanonicalResidue.reduction,if_neg hu]
    rfl

theorem rawGraph_iff (z : Fin 2 → M) : z ∈ rawGraph (M := M) ↔
    ∃ u : Values.presentationValuation.valuationSubring,
      u.val.val = z 0 ∧
        (residueRV (IsLocalRing.residue Values.presentationValuation.valuationSubring u)).val = z 1 := by
  constructor
  · intro hz
    let x : VFType (M := M) := ⟨z 0,hz.1⟩
    have hx : Values.presentationValuation x ≤ 1 := by
      have h := hz.2.1
      have hrv : iRv (1 : VFType (M := M)).val = iRVOne := RVCalc.rv_one hM
      have hp : VFValued.predV x 1 := by
        change iLe (iRv (1 : VFType (M := M)).val) (iRv x.val)
        exact hrv.symm ▸ h
      simpa only [map_one] using (Values.presentation_compatible x 1).mp hp
    let u : Values.presentationValuation.valuationSubring :=
      ⟨x,(Valuation.mem_valuationSubring_iff _ _).mpr hx⟩
    have he : (![u.val.val,z 1] : Fin 2 → M) = z := by
      funext i
      fin_cases i <;> rfl
    exact ⟨u,rfl,((residue_iff u (z 1)).mp (he.symm ▸ hz)).symm⟩
  · rintro ⟨u,hu0,hu1⟩
    have hz := (residue_iff u (z 1)).mpr hu1.symm
    have he : (![u.val.val,z 1] : Fin 2 → M) = z := by
      funext i
      fin_cases i
      · exact hu0
      · rfl
    exact he ▸ hz

theorem coordinate_iff (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : BallResidueChart.Point a α) (t : ModelResidue M) :
    (![((x.val-a)/r).val,(residueRV t).val] : Fin 2 → M) ∈ rawGraph (M := M) ↔
      t = BallResidueChart.coordinate a r α hr x := by
  let u := IntegrationInACVF.Section3.AffineResidueChart.integral Values.presentationValuation a r
    (BallResidueChart.representative_ne_zero r α hr) (BallResidueChart.fieldPoint a r α hr x)
  change (![u.val.val,(residueRV t).val] : Fin 2 → M) ∈ rawGraph (M := M) ↔ _
  rw [residue_iff]
  constructor
  · intro he
    exact residueRV_injective (Subtype.ext he)
  · intro he
    exact congrArg (fun c => (residueRV c).val) he

end IntegrationInACVF.Section3ACVF.ResidueReductionSyntax
