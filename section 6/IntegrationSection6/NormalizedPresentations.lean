import IntegrationSection6.CanonicalNormalization
import Section5.PullbackLift

/-! Transport actual mixed presentations through a second normalization.
The carrier, graph and original parameter set are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m u w : ℕ}

/-- Exactly the same point set, presented after normalizing the ambient model. -/
def normalizedPointSet (A : DefSet (M := M) S n m) :
    @DefSet M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) S n m := by
  let C : Set (Point (M := M) n m) := carrier A
  let T : Set ((Fin n ⊕ Fin m) → M) :=
    @SpecialTransformations.DefinableGeometry.Space.preimage LRV M
      (@CanonicalStructure.normalize M sM) (@pointSpace M sM hM n m) C
  refine @SpecialTransformations.DefinableGeometry.DefSet.mk LRV M
    (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM))
    (@pointSpace M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) n m) S C ?_
  change @Set.Definable M S LRV
      (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) (Fin n ⊕ Fin m) T
  rw [normalized_structure_idempotent]
  exact setDefinable A

/-- The complete original graph is retained, including all target representatives. -/
def normalizedPointMap {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (f : Map A B) :
    @Map M (@CanonicalStructure.normalize M sM) _ _ S
      (normalizedPointSet A) (normalizedPointSet B) := by
  let T : Set (((Fin n ⊕ Fin m) ⊕ (Fin u ⊕ Fin w)) → M) :=
    @SpecialTransformations.DefinableGeometry.Space.relation LRV M
      (@CanonicalStructure.normalize M sM) (@pointSpace M sM hM n m)
      (@pointSpace M sM hM u w) (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y)
  refine @SpecialTransformations.DefinableGeometry.Map.mk LRV M
    (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM)) _ _ S _ _
    (fun a => ⟨(f ⟨a.val,a.property⟩).val,(f ⟨a.val,a.property⟩).property⟩) ?_
  change @Set.Definable M S LRV
      (@CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM))
      ((Fin n ⊕ Fin m) ⊕ (Fin u ⊕ Fin w)) T
  rw [normalized_structure_idempotent]
  exact Map.graph_definable f

end IntegrationInACVF.Section6
