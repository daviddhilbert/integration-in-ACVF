import IntegrationSection6.GammaFormulaTypedRows
import IntegrationSection6.GammaMixedTupleGraphs
import IntegrationSection6.GammaRawElementaryRowCoordinates

/-! Interpret primitive formulas as full RV families over pure VF parameters.
The relation flattening only reassociates coordinates and retains properness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

theorem gammaPointSort_vf_zero (p : ℕ) : gammaPointSort p 0 = (fun _ => SortTag.vf) := by
  funext j
  exact Fin.append_left _ _ j

theorem gammaPointCode_vf_zero (z : Point (M := M) p 0) :
    gammaPointCode z = (fun j => (z.1 j).val) := by
  funext j
  exact Fin.append_left _ _ j

def GammaDomainFormula.vfRelation (D : GammaDomainFormula B p a (fun _ => .vf))
    (z : Point (M := M) p 0) (x : Point (M := M) 0 a) : Prop :=
  Fin.append (fun j => (z.1 j).val) (fun j => (x.2 j).val) ∈ D.val

theorem GammaDomainFormula.vfRelation_definable
    (D : GammaDomainFormula B p a (fun _ => .vf)) : GammaGraphDefinable B D.vfRelation := by
  have hd : DefinableOverBase B (Fin.append (gammaPointSort p 0) (fun _ : Fin a => .rv)) D.val := by
    simpa only [Nat.add_zero,gammaPointSort_vf_zero] using D.property
  have h := gamma_mixed_rv_graph_from_tuple_formula (p := p) (a := 0) (k := a) hd
  apply GammaGraphDefinable.congr h
  intro z x
  rw [gammaPointCode_vf_zero]
  rfl

def GammaRelationFormula.flatten (R : GammaRelationFormula B p a b (fun _ => .vf)) :
    GammaDomainFormula B p (a+b) (fun _ => .vf) :=
  ⟨{w | w ∘ Fin.cast (Nat.add_assoc p a b) ∈ R.val ∧
    w ∈ sortedUniverse (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin (a+b) => .rv))},
    R.property.preimage_real _ (Fin.cast (Nat.add_assoc p a b))⟩

def GammaRelationFormula.vfRelation (R : GammaRelationFormula B p a b (fun _ => .vf)) :=
  R.flatten.vfRelation

theorem GammaRelationFormula.vfRelation_definable
    (R : GammaRelationFormula B p a b (fun _ => .vf)) : GammaGraphDefinable B R.vfRelation :=
  R.flatten.vfRelation_definable

theorem GammaRelationFormula.vfRelation_append
    (R : GammaRelationFormula B p a b (fun _ => .vf)) (z : Point (M := M) p 0)
    (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)) :
    R.vfRelation z (Fin.elim0,Fin.append x y) ↔
      Fin.append (Fin.append (fun j => (z.1 j).val) (fun j => (x j).val))
        (fun j => (y j).val) ∈ R.val := by
  change (_ ∈ R.val ∧ _ ∈ sortedUniverse _) ↔ _
  have hv : (fun j => ((Fin.append x y) j).val) =
      Fin.append (fun j => (x j).val) (fun j => (y j).val) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  rw [hv,← Fin.append_assoc]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    have hp := sorted_append_RV (fun _ : Fin p => .vf) (fun j => (z.1 j).val)
      (fun j => (z.1 j).property) (Fin.append x y)
    simpa only [hv] using hp

end IntegrationInACVF.Section6
