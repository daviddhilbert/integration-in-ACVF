import IntegrationSection6.GammaFormulaVFFamilies
import IntegrationSection6.GammaSchemaFiniteRows
import IntegrationSection6.GammaGlobalRestriction
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.GammaVFAllFinitePresentation

/-! The literal total lift of a finite RV[k] family over a VF base.
The parameter coordinates are kept, and the new VF block lifts the row's
volume tuple. Full original-Gamma definitions and finite RV fibres follow. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def familyLiftCoordinatesMap (S : Set M) (p a k : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) (p+k) a) S)
      (PresentedSet.univ (pointSpace (M := M) p (a+k)) S) :=
  @Map.comp M sM _ _ _ S _ _ _
    (mixedCoordinatePointMap (Fin.castAdd k)
      (Fin.addCases (fun j => Fin.natAdd (p+k) j) (fun j => Fin.castAdd a (Fin.natAdd p j))) S)
    (canonicalMap (PresentedSet.univ (pointSpace (M := M) (p+k) a) S))

theorem familyLiftCoordinatesMap_value (S : Set M)
    (q : PresentedSet.univ (pointSpace (M := M) (p+k) a) S) :
    (familyLiftCoordinatesMap S p a k q).val =
      (q.val.1 ∘ Fin.castAdd k,Fin.append q.val.2 (tupleRV (q.val.1 ∘ Fin.natAdd p))) := by
  apply Prod.ext
  · rfl
  change (Fin.append (tupleRV q.val.1) q.val.2 ∘
    (Fin.addCases (fun j => Fin.natAdd (p+k) j) (fun j => Fin.castAdd a (Fin.natAdd p j)))) = _
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Fin.addCases_left,Fin.addCases_right,Function.comp_apply,Fin.append_left,Fin.append_right,tupleRV]

def familyLiftDomain (A : Set (Point (M := M) p 0)) (F : GammaFiniteRVSchema B p a k) :
    Set (Point (M := M) (p+k) a) :=
  {q | (q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ A ∧
    F.rowVolume (fun j => (q.1 (Fin.castAdd k j)).val) q.2 (tupleRV (q.1 ∘ Fin.natAdd p))}

theorem gamma_family_lift_definable (A : Set (Point (M := M) p 0))
    (hA : GammaSetDefinable B A) (F : GammaFiniteRVSchema B p a k) :
    GammaSetDefinable B (familyLiftDomain A F) := by
  let R : GammaRelationFormula B p a k (fun _ => .vf) := ⟨F.volume,F.volume_definable⟩
  have hR := gamma_set_of_sorted_formula R.flatten.property
  have hV := gamma_global_preimage (familyLiftCoordinatesMap B.real p a k) hR
  have hBase := gamma_global_preimage
    (mixedCoordinatePointMap (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin a) B.real) hA
  have h := (gammaLogicInput B).inter hBase hV
  convert h using 1
  ext q
  change ((q.1 ∘ Fin.castAdd k,Fin.elim0) ∈ A ∧
    F.rowVolume (fun j => (q.1 (Fin.castAdd k j)).val) q.2 (tupleRV (q.1 ∘ Fin.natAdd p))) ↔
    ((q.1 ∘ Fin.castAdd k,q.2 ∘ (Fin.elim0 : Fin 0 → Fin a)) ∈ A ∧
      gammaPointCode (familyLiftCoordinatesMap B.real p a k ⟨q,Set.mem_univ _⟩).val ∈ R.flatten.val)
  have hb : (q.1 ∘ Fin.castAdd k,q.2 ∘ (Fin.elim0 : Fin 0 → Fin a)) =
      (q.1 ∘ Fin.castAdd k,Fin.elim0) := Prod.ext rfl (Subsingleton.elim _ _)
  rw [hb]
  apply and_congr Iff.rfl
  rw [familyLiftCoordinatesMap_value]
  exact (R.vfRelation_append (q.1 ∘ Fin.castAdd k,Fin.elim0) q.2
    (tupleRV (q.1 ∘ Fin.natAdd p))).symm

def gammaFamilyLift (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val)) : FiniteRV.GammaVFAllFiniteObject B where
  arity := (p+k,a)
  domain := familyLiftDomain A F
  definable := gamma_family_lift_definable A hA F
  finiteFibres := by
    intro x
    by_cases hx : (x ∘ Fin.castAdd k,Fin.elim0) ∈ A
    · exact ((hF ⟨(x ∘ Fin.castAdd k,Fin.elim0),hx⟩).2.2
        (tupleRV (x ∘ Fin.natAdd p))).subset (fun r hr => hr.2)
    · have he : {t | (x,t) ∈ familyLiftDomain A F} = ∅ := by
        ext t
        exact ⟨fun h => False.elim (hx h.1),False.elim⟩
      rw [he]
      exact Set.finite_empty

end IntegrationInACVF.Section6
