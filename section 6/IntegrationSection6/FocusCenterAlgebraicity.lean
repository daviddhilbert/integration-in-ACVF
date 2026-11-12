import IntegrationSection6.LiftPresentations
import Section5.RootConstruction
import Section5.Assembly
import Section4.MapAlgebraicity
import Section3.CanonicalParameters

/-! The independence condition in a genuine focus removes the active VF
coordinate from the algebraicity base of its centre's RV class. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- Erase the active field coordinate using the named field zero. -/
def erasePointMap (A : DefSet (M := M) S n m) (j : Fin n) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (erase j)
    (fun z => Sum.elim (fun i => if i = j then iVFZero else z (.inl i))
      (fun i => z (.inr i)))
    (by
      intro i
      cases i with
      | inl i =>
        by_cases hi : i = j
        · simpa [hi] using (zeroCode_definable S : RawFun S (Fin n ⊕ Fin m) (fun _ => iVFZero))
        · simpa [hi] using rawProj S (.inl i : Fin n ⊕ Fin m)
      | inr i => exact rawProj S (.inr i : Fin n ⊕ Fin m))
    (by
      intro c
      refine ⟨?_, c.property.2⟩
      intro i
      by_cases hi : i = j
      · simpa [Function.comp_apply, hi] using
          (show sortEval .vf (iVFZero : M) from (0 : VF (M := M)).property)
      · simpa [hi, Function.comp_def] using c.property.1 i)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext i
      apply Subtype.ext
      by_cases hi : i = j <;> simp [erase, replace, hi])

/-- Add the unique empty RV tuple to a scalar field tuple. -/
def scalarPointMap (S : Set M) :
    Map (PresentedSet.univ (SpecialTransformations.Section4.vfSpace (M := M) 1) S)
      (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.ofCodes _ (fun a => (a, Fin.elim0))
    (fun z => Sum.elim z Fin.elim0)
    (by intro i; cases i with
        | inl i => exact rawProj S i
        | inr i => exact i.elim0)
    (by intro c; exact ⟨c.property, fun i => i.elim0⟩)
    (by intro c; exact Prod.ext rfl (Subsingleton.elim _ _))

variable {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}

def erasedRawMap (D : Focus A j k) :
    Map D.active (PresentedSet.univ (rawPointSpace n m) S) :=
  Map.comp (rawPointMap _) (erasePointMap D.active j)

def centerRawMap (D : Focus A j k) :
    Map D.active (PresentedSet.univ (rawPointSpace 1 0) S) :=
  Map.comp (rawPointMap _) (Map.comp (scalarPointMap S) D.centerMap)

theorem centerRawMap_constant (D : Focus A j k) (a b : D.active)
    (he : (erasedRawMap D a).val = (erasedRawMap D b).val) :
    centerRawMap D a = centerRawMap D b := by
  apply Subtype.ext
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  have h : erase j a.val = erase j b.val := he
  have hc := D.independent a.val a.property b.val b.property h
  change ![D.center a.val] = ![D.center b.val]
  rw [hc]

/-- The actual descended definable centre, over the actual erased image. -/
def descendedCenter (D : Focus A j k) :
    Map (Map.image (erasedRawMap D)) (PresentedSet.univ (rawPointSpace 1 0) S) :=
  Map.descend (erasedRawMap D) (centerRawMap D) (centerRawMap_constant D)

theorem descendedCenter_apply (D : Focus A j k) (a : D.active) :
    descendedCenter D (Map.toImage (erasedRawMap D) a) = centerRawMap D a :=
  Map.descend_apply _ _ _ a

/-- Input RV names are eliminated by the inherited algebraicity theorem;
the active VF coordinate was erased before applying it. -/
theorem center_algebraic_erased (D : Focus A j k) (a : D.active) :
    AlgebraicAt (S ∪ Set.range (fun i => ((erase j a.val).1 i).val)) .rv
      (rv (D.center a.val)).val := by
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  let hN := @CanonicalStructure.normalized_model M sM hM
  have h := @SpecialTransformations.Section4.map_output_rv_algebraic M N hN S n m 1 0
    (@CanonicalStructure.normalize_isCanonical M sM)
    (Map.image (erasedRawMap D)) (PresentedSet.univ (rawPointSpace 1 0) S)
    (descendedCenter D) (Map.toImage (erasedRawMap D) a) 0
  rw [descendedCenter_apply] at h
  apply (algebraicAt_normalize_iff _ .rv _).mp
  convert h using 1
  all_goals first
    | rfl
    | exact (rvCode_eq (D.center a.val).val (D.center a.val).property).symm

end IntegrationInACVF.Section6
