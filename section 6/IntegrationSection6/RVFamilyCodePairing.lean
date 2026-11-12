import Section5.Assembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m a b : ℕ} {A : DefSet (M := M) S n m}

theorem pairRVMaps_label_left (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 a) S))
    (g : Map A (PresentedSet.univ (pointSpace (M := M) 0 b) S)) (x : A) (j : Fin a) :
    (pairRVMaps f g x).val.2 (Fin.castAdd b j) = (f x).val.2 j := by
  change Fin.append (f x).val.2 (g x).val.2 (Fin.castAdd b j) = _
  exact Fin.append_left _ _ _

theorem pairRVMaps_label_right (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 a) S))
    (g : Map A (PresentedSet.univ (pointSpace (M := M) 0 b) S)) (x : A) (j : Fin b) :
    (pairRVMaps f g x).val.2 (Fin.natAdd a j) = (g x).val.2 j := by
  change Fin.append (f x).val.2 (g x).val.2 (Fin.natAdd a j) = _
  exact Fin.append_right _ _ _

theorem pairRVMaps_eq_left (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 a) S))
    (g : Map A (PresentedSet.univ (pointSpace (M := M) 0 b) S)) {x y : A}
    (h : pairRVMaps f g x = pairRVMaps f g y) : f x = f y := by
  apply Subtype.ext
  apply Prod.ext (Subsingleton.elim _ _)
  funext j
  have hh := congrArg (fun q : PresentedSet.univ (pointSpace (M := M) 0 (a+b)) S => q.val.2 (Fin.castAdd b j)) h
  simpa only [pairRVMaps_label_left] using hh

theorem pairRVMaps_eq_right (f : Map A (PresentedSet.univ (pointSpace (M := M) 0 a) S))
    (g : Map A (PresentedSet.univ (pointSpace (M := M) 0 b) S)) {x y : A}
    (h : pairRVMaps f g x = pairRVMaps f g y) : g x = g y := by
  apply Subtype.ext
  apply Prod.ext (Subsingleton.elim _ _)
  funext j
  have hh := congrArg (fun q : PresentedSet.univ (pointSpace (M := M) 0 (a+b)) S => q.val.2 (Fin.natAdd a j)) h
  simpa only [pairRVMaps_label_right] using hh

end IntegrationInACVF.Section6
