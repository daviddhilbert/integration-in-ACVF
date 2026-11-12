import IntegrationSection6.MixedRVBlockEquivalences
import IntegrationSection6.GammaRealImages
import IntegrationSection6.GammaPreparedDescent

/-! The actual canonical key embedding, reassociated so the full prepared
base key precedes the unchanged fibre RV labels. -/
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
variable {p l a : ℕ}

def preparedKeyExtensionMap (S : Set M) (p l a : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p (l+a)) S)
      (PresentedSet.univ (pointSpace (M := M) p ((p+l)+a)) S) :=
  @Map.comp M sM _ _ _ S _ _ _
    (mixedCoordinatePointMap (id : Fin p → Fin p)
      (Fin.cast (Nat.add_assoc p l a) : Fin ((p+l)+a) → Fin (p+(l+a))) S)
    (canonicalMap (PresentedSet.univ (pointSpace (M := M) p (l+a)) S))

theorem preparedKeyExtensionMap_value (S : Set M)
    (x : PresentedSet.univ (pointSpace (M := M) p (l+a)) S) :
    (preparedKeyExtensionMap S p l a x).val =
      (x.val.1,Fin.append (flatKey (mixedRVBase x.val)).2 (mixedRVTail x.val)) := by
  change (x.val.1,Fin.append (fun j => rv (x.val.1 j)) x.val.2 ∘ Fin.cast (Nat.add_assoc p l a)) =
    (x.val.1,Fin.append (Fin.append (fun j => rv (x.val.1 j)) (x.val.2 ∘ Fin.castAdd a))
      (x.val.2 ∘ Fin.natAdd l))
  have he := Fin.append_assoc (fun j => rv (x.val.1 j)) (x.val.2 ∘ Fin.castAdd a) (x.val.2 ∘ Fin.natAdd l)
  simp only [Function.comp_def] at he
  rw [Fin.append_castAdd_natAdd (f := x.val.2)] at he
  exact congrArg (fun r : Fin ((p+l)+a) → RV (M := M) => (x.val.1,r)) he.symm

theorem preparedKeyExtensionMap_injective (S : Set M) :
    Function.Injective (preparedKeyExtensionMap S p l a) := by
  intro x y h
  have hv := congrArg (fun z => z.val) h
  apply Subtype.ext
  apply canonical_injective
  have hf : (canonical x.val).1 = (canonical y.val).1 :=
    congrArg (fun z : Point (M := M) p ((p+l)+a) => z.1) hv
  apply Prod.ext (x := canonical x.val) (y := canonical y.val) hf
  have hr := congrArg (fun z : Point (M := M) p ((p+l)+a) => z.2) hv
  change (canonical x.val).2 ∘ Fin.cast (Nat.add_assoc p l a) =
    (canonical y.val).2 ∘ Fin.cast (Nat.add_assoc p l a) at hr
  funext j
  have hh := congrFun hr (Fin.cast (Nat.add_assoc p l a).symm j)
  simpa only [Function.comp_apply,Fin.cast_cast,Fin.cast_eq_self] using hh

end IntegrationInACVF.Section6
