import IntegrationSection6.RootSelection
import Section4.RVLabelCompression

/-! A root selector exists on a real-base definable ambient domain before
restricting it to a possibly Gamma-definable source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

/-- All field RV coordinates, with the old RV labels omitted. -/
def fieldRVMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (rawRVSpace n) S) :=
  Map.comp (rawRVProjectionMap (Fin.castAdd m) (PresentedSet.univ (rawRVSpace (n+m)) S))
    (rawKeyMap (PresentedSet.univ (pointSpace n m) S))

@[simp] theorem fieldRVMap_value (S : Set M) (n m : ℕ)
    (a : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (fieldRVMap S n m a).val = fun i => rv (a.val.1 i) := by
  funext i
  exact Fin.append_left _ _ i

/-- The whole domain on which this real-base equation defines a unique
root in the specified RV fibre. No source object occurs in this definition. -/
def rootSelectionDomain (S : Set M) {n : ℕ} (m : ℕ) (R : Set (Fin n → M))
    (hR : @Set.Definable M S LRV N (Fin n) R) (j : Fin n) : DefSet (M := M) S n m :=
  PresentedSet.mk {p | (fun i => (rv (p.1 i)).val) ∈ @rootDomain M N n R j} (by
    let F := fieldRVMap (M := M) S n m
    let C : PresentedSet (rawRVSpace n) S :=
      @SpecialTransformations.Section4.rvDefSetOfCode M N S n
        (@rootDomain M N n R j) (@rootDomain_definable M N n S R hR j)
    have h := Map.definable_preimage F (setDefinable C)
    convert h using 1
    ext p
    constructor
    · intro hp
      refine ⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩
      change (fun i => ((fieldRVMap S n m ⟨p,Set.mem_univ _⟩).val i).val) ∈ @rootDomain M N n R j
      rwa [fieldRVMap_value]
    · rintro ⟨a,rfl,ha⟩
      change (fun i => ((fieldRVMap S n m a).val i).val) ∈ @rootDomain M N n R j at ha
      rwa [fieldRVMap_value] at ha)

@[simp] theorem rootSelectionDomain_mem (S : Set M) {n : ℕ} (m : ℕ)
    (R : Set (Fin n → M)) (hR : @Set.Definable M S LRV N (Fin n) R) (j : Fin n)
    (p : Point (M := M) n m) :
    p ∈ carrier (rootSelectionDomain S m R hR j) ↔
      (fun i => (rv (p.1 i)).val) ∈ @rootDomain M N n R j := Iff.rfl

end IntegrationInACVF.Section6
