import IntegrationSection6.ElementaryIsomorphism
import IntegrationSection6.KeyInverseCoordinates

/-! Old labels and the auxiliary RV parameter are literal coordinate projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem elementaryProjection_labels (U : RVObject (M := M) S n) (i : Fin n)
    (a : (elementary U i).domain) :
    (elementaryProjection U i a).val = fun j => a.val (Fin.castAdd 1 j) := by
  have h := elementary_labels U i a
  funext j
  exact (Fin.append_left _ _ j).symm.trans (congrFun h (Fin.castAdd 1 j)).symm

theorem elementaryParameter_labels (U : RVObject (M := M) S n) (i : Fin n)
    (a : (elementary U i).domain) :
    (elementaryParameter U i a).val = fun j => a.val (Fin.natAdd U.arity j) := by
  have h := elementary_labels U i a
  funext j
  exact (Fin.append_right _ _ j).symm.trans (congrFun h (Fin.natAdd U.arity j)).symm

theorem elementaryMap_labels {U V : RVObject (M := M) S n} (i j : Fin n)
    (f : Map U.domain V.domain) (a : (elementary U i).domain) :
    (elementaryMap i j f a).val =
      Fin.append (f (elementaryProjection U i a)).val (fun l => a.val (Fin.natAdd U.arity l)) := by
  rw [elementary_labels V j,elementaryMap_projection,elementaryMap_parameter,elementaryParameter_labels]
  rfl

end IntegrationInACVF.Section6
