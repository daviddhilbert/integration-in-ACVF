module

public import Integration7.FactoredRVConstraintHeadMaps
public import Section5.Assembly

@[expose] public section

/-! A pure RV graph extension has a genuine inverse to its old-label
projection. The additional labels are retained in the actual domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {l e : ℕ}

def pureRVLabelGraphMap (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) := pairRVMaps (Map.id Q) g

def pureRVLabelGraph (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) : DefSet (M := M) S 0 (l+e) :=
  Map.image (pureRVLabelGraphMap Q g)

theorem pure_rv_label_graph_bijective (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) :
    Function.Bijective (Map.toImage (pureRVLabelGraphMap Q g)) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply Prod.ext (Subsingleton.elim _ _)
    funext i
    have h := congrArg (fun q : pureRVLabelGraph Q g => q.val.2 (Fin.castAdd e i)) huv
    change Fin.append u.val.2 (g u).val.2 (Fin.castAdd e i) =
      Fin.append v.val.2 (g v).val.2 (Fin.castAdd e i) at h
    simpa only [Fin.append_left] using h
  · rintro ⟨q,u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

def pureRVLabelGraphInverse (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) : Map (pureRVLabelGraph Q g) Q :=
  Map.inverse (Map.toImage (pureRVLabelGraphMap Q g)) (pure_rv_label_graph_bijective Q g)

theorem pure_rv_label_graph_inverse_bijective (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) :
    Function.Bijective (pureRVLabelGraphInverse Q g) := by
  constructor
  · intro u v huv
    have h := congrArg (Map.toImage (pureRVLabelGraphMap Q g)) huv
    simpa only [pureRVLabelGraphInverse,Map.apply_inverse] using h
  · intro u
    exact ⟨Map.toImage (pureRVLabelGraphMap Q g) u,Map.inverse_apply _ _ u⟩

theorem pure_rv_label_graph_inverse_labels (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) (q : pureRVLabelGraph Q g) :
    (pureRVLabelGraphInverse Q g q).val.2=q.val.2 ∘ Fin.castAdd e := by
  have h := congrArg (fun z : pureRVLabelGraph Q g => z.val.2)
    (Map.apply_inverse (Map.toImage (pureRVLabelGraphMap Q g)) (pure_rv_label_graph_bijective Q g) q)
  change Fin.append (pureRVLabelGraphInverse Q g q).val.2 (g (pureRVLabelGraphInverse Q g q)).val.2=q.val.2 at h
  funext i
  exact (Fin.append_left _ _ i).symm.trans (congrFun h (Fin.castAdd e i))
end IntegrationInACVF.Section7
