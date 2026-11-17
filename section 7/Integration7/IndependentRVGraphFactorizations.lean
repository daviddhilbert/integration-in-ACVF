module

public import Integration7.PureRVLabelGraphFactorizations
public import Integration7.IndependentRVSpecialSources

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The independent coefficient constraint, with arbitrary functional
RV labels appended, has an actual factorization into old source labels
and the unchanged coefficient. This constructs the pure-RV input of the
factored head theorem instead of assuming a fibre-integral identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a d e : ℕ}
variable (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (a : ℕ) (R : DefSet (M := M) (C.base : Set M) 0 d)

def independentRVConstraintFactorization :
    Map (independentRVLabelConstraint C Ξ hNames a R)
      (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) (C.base : Set M)) R) := by
  let Q := independentRVLabelConstraint C Ξ hNames a R
  let J : Map Q (PresentedSet.univ (pointSpace (M := M) 0 (a+d)) (C.base : Set M)) := Map.inclusion (fun _ _ => Set.mem_univ _)
  let first := Map.comp (rvCoordinatePointMap (Fin.castAdd d : Fin a → Fin (a+d)) (C.base : Set M)) J
  let second := mapIntoSubset (Map.comp (rvCoordinatePointMap (Fin.natAdd a : Fin d → Fin (a+d)) (C.base : Set M)) J)
    R (fun q => (independent_rv_label_constraint_mem C Ξ hNames a R q.val).mp q.property)
  exact Map.pair first second

theorem independent_rv_constraint_factorization_bijective :
    Function.Bijective (independentRVConstraintFactorization C Ξ hNames a R) := by
  constructor
  · intro u v huv
    have h := congrArg Subtype.val huv
    apply Subtype.ext
    apply Prod.ext (Subsingleton.elim _ _)
    funext i
    cases i using Fin.addCases with
    | left i => exact congrArg (fun z : Point (M := M) 0 a × Point (M := M) 0 d => z.1.2 i) h
    | right i => exact congrArg (fun z : Point (M := M) 0 a × Point (M := M) 0 d => z.2.2 i) h
  · intro q
    let labels := Fin.append q.val.1.2 q.val.2.2
    have hm : (Fin.elim0,labels) ∈ carrier (independentRVLabelConstraint C Ξ hNames a R) := by
      apply (independent_rv_label_constraint_mem C Ξ hNames a R _).mpr
      have he : (Fin.elim0,labels ∘ Fin.natAdd a)=q.val.2 :=
        Prod.ext (Subsingleton.elim _ _) (funext (Fin.append_right _ _))
      exact he.symm ▸ q.property.2
    refine ⟨⟨(Fin.elim0,labels),hm⟩,Subtype.ext ?_⟩
    exact Prod.ext (Prod.ext (Subsingleton.elim _ _) (funext (Fin.append_left _ _)))
      (Prod.ext (Subsingleton.elim _ _) (funext (Fin.append_right _ _)))

variable (g : Map (independentRVLabelConstraint C Ξ hNames a R)
  (PresentedSet.univ (pointSpace (M := M) 0 e) (C.base : Set M)))

def independentRVGraphFactorization :
    Map (pureRVLabelGraph (independentRVLabelConstraint C Ξ hNames a R) g)
      (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) (C.base : Set M)) R) :=
  Map.comp (independentRVConstraintFactorization C Ξ hNames a R)
    (pureRVLabelGraphInverse (independentRVLabelConstraint C Ξ hNames a R) g)

theorem independent_rv_graph_factorization_bijective :
    Function.Bijective (independentRVGraphFactorization C Ξ hNames a R g) :=
  (independent_rv_constraint_factorization_bijective C Ξ hNames a R).comp
    (pure_rv_label_graph_inverse_bijective _ g)

theorem independent_rv_graph_factorization_old_labels
    (q : pureRVLabelGraph (independentRVLabelConstraint C Ξ hNames a R) g) :
    (independentRVGraphFactorization C Ξ hNames a R g q).val.1.2 =
      q.val.2 ∘ (Fin.castAdd e ∘ Fin.castAdd d) := by
  change (pureRVLabelGraphInverse _ g q).val.2 ∘ Fin.castAdd d = _
  rw [pure_rv_label_graph_inverse_labels]
  rfl

theorem independent_rv_graph_factorization_coefficient_labels
    (q : pureRVLabelGraph (independentRVLabelConstraint C Ξ hNames a R) g) :
    (independentRVGraphFactorization C Ξ hNames a R g q).val.2.2 =
      q.val.2 ∘ (Fin.castAdd e ∘ Fin.natAdd a) := by
  change (pureRVLabelGraphInverse _ g q).val.2 ∘ Fin.natAdd a = _
  rw [pure_rv_label_graph_inverse_labels]
  rfl
end IntegrationInACVF.Section7
