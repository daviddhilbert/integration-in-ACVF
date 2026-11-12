import IntegrationSection6.GammaFormulaVFFamilies
import IntegrationSection6.GammaPreparedDescent

/-! Primitive formulas descend along a genuine Gamma special bijection
of the VF base to full Gamma formulas on its RV key space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b q : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}

def GammaDomainFormula.preparedDescend (D : GammaDomainFormula B p a (fun _ => .vf))
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain) :
    GammaDomainFormula B (p+l) a (fun _ => .rv) := by
  let r := rvDescendedRelation C (fun x z => D.vfRelation (T.inverseMap x).val z)
  refine ⟨gammaRawRVGraph r,?_⟩
  have h := gammaRawRVGraph_definable (gamma_prepared_rv_descent T hT D.vfRelation D.vfRelation_definable)
  have hs : Fin.append (fun _ : Fin (p+l) => SortTag.rv) (fun _ : Fin a => SortTag.rv) =
      (fun _ => SortTag.rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  rw [hs]
  exact h

theorem GammaDomainFormula.preparedDescend_row
    (D : GammaDomainFormula B p a (fun _ => .vf))
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hrows : ∀ x y : C, SameRV x.val y.val → ∀ z,
      D.vfRelation (T.inverseMap x).val z ↔ D.vfRelation (T.inverseMap y).val z)
    (x : C) (u : Fin a → RV (M := M)) :
    Fin.append (fun j => ((flatKey x.val).2 j).val) (fun j => (u j).val) ∈
      (D.preparedDescend T hT).val ↔ D.vfRelation (T.inverseMap x).val (Fin.elim0,u) := by
  change _ ∈ gammaRawRVGraph _ ↔ _
  exact (gammaRawRVGraph_append_iff _ (flatKey x.val) (Fin.elim0,u)).trans
    (rvDescendedRelation_spec C _ hrows x (Fin.elim0,u))

def GammaDomainFormula.unflattenRV (D : GammaDomainFormula B q (a+b) (fun _ => .rv)) :
    GammaRelationFormula B q a b (fun _ => .rv) :=
  ⟨{w | w ∘ Fin.cast (Nat.add_assoc q a b).symm ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append (fun _ : Fin q => .rv)
        (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv))},
    D.property.preimage_real _ (Fin.cast (Nat.add_assoc q a b).symm)⟩

theorem GammaDomainFormula.unflattenRV_append
    (D : GammaDomainFormula B q (a+b) (fun _ => .rv))
    (t : Fin q → RV (M := M)) (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)) :
    Fin.append (Fin.append (fun j => (t j).val) (fun j => (x j).val)) (fun j => (y j).val) ∈
        D.unflattenRV.val ↔
      Fin.append (fun j => (t j).val) (fun j => ((Fin.append x y) j).val) ∈ D.val := by
  change (_ ∈ D.val ∧ _ ∈ sortedUniverse _) ↔ _
  have hv : (fun j => ((Fin.append x y) j).val) =
      Fin.append (fun j => (x j).val) (fun j => (y j).val) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  have he : Fin.append (Fin.append (fun j => (t j).val) (fun j => (x j).val))
        (fun j => (y j).val) ∘ Fin.cast (Nat.add_assoc q a b).symm =
      Fin.append (fun j => (t j).val) (Fin.append (fun j => (x j).val) (fun j => (y j).val)) := by
    rw [Fin.append_assoc,Function.comp_assoc]
    have hc : Fin.cast (Nat.add_assoc q a b) ∘ Fin.cast (Nat.add_assoc q a b).symm = id := by
      funext j
      exact Fin.ext rfl
    rw [hc,Function.comp_id]
  rw [he,hv]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    exact sorted_append_RV _ _ (sorted_append_RV (fun _ : Fin q => .rv)
      (fun j => (t j).val) (fun j => (t j).property) x) y

def GammaParameterRecode.prepared (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) :
    GammaParameterRecode B p (p+l) (fun _ => .vf) (fun _ => .rv) where
  domain D := D.preparedDescend T hT
  relation R := (R.flatten.preparedDescend T hT).unflattenRV

end IntegrationInACVF.Section6
