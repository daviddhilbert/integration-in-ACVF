import IntegrationSection5.PartialContractionProgram
import IntegrationSection5.NaturalContractionCoordinates

/-! The natural partial contraction map retains its frozen VF parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {p n m l : ℕ}

/-- The active coordinates precede the frozen coordinates. -/
def activeIndex (p n : ℕ) (i : Fin n) : Fin (p+n) := ⟨i.val,by omega⟩

def frozenIndex (p : ℕ) : (n : ℕ) → Fin p → Fin (p+n)
  | 0 => id
  | n+1 => fun i => (frozenIndex p n i).succ

namespace PartialContractionProgram
variable {A : DefSet (M := M) S (p+n) m} {U : DefSet (M := M) S p l}

def naturalMap {a b c : ℕ} {X : DefSet (M := M) S (p+a) b} {Y : DefSet (M := M) S p c}
    (T : PartialContractionProgram S p (n := a) X Y) : Map X (PresentedSet.univ (pointSpace (p+a) c) S) := by
  induction T with
  | zero A => exact Map.inclusion (Set.subset_univ _)
  | step T tail ih =>
    exact Map.comp (insertHeadMap S _ _)
      (Map.pair (Map.comp (firstVFMap T.target) T.map) (Map.comp ih T.contractionMap))

theorem naturalMap_zero {A : DefSet (M := M) S p m} (a : A) :
    ((zero A).naturalMap a).val = a.val := rfl

theorem naturalMap_step {a b c : ℕ} {X : DefSet (M := M) S ((p+a)+1) b} {Y : DefSet (M := M) S p c}
    (T : HeadPreparation X) (tail : PartialContractionProgram S p (n := a) T.contractedSet Y) (x : X) :
    ((step T tail).naturalMap x).val =
      insertHead (vfAt (T.map x).val 0) (tail.naturalMap (T.contractionMap x)).val := rfl

theorem naturalMap_labels (T : PartialContractionProgram S p (n := n) A U) (a : A) :
    (T.naturalMap a).val.2 = (T.toMap a).val.2 := by
  induction T with
  | zero A => rfl
  | step T tail ih => exact ih (T.contractionMap a)

theorem naturalMap_rv (T : PartialContractionProgram S p (n := n) A U) (a : A) (i : Fin n) :
    (T.toMap a).val.2 (T.volumeIndex i) = rv (vfAt (T.naturalMap a).val (activeIndex p n i)) := by
  induction T with
  | zero A => exact Fin.elim0 i
  | @step n m l A U T tail ih =>
    cases i using Fin.cases with
    | zero =>
      have h := tail.oldLabels (T.contractionMap a) (0 : Fin (1+T.arity))
      refine h.trans ?_
      have hk := congrArg (fun p : Point (M := M) (p+n) (1+T.arity) => p.2 (Fin.castAdd T.arity 0))
        (headKeyMap_apply T.target (T.map a))
      exact hk
    | succ i => exact ih (T.contractionMap a) i

theorem naturalMap_injective (T : PartialContractionProgram S p (n := n) A U) : Function.Injective T.naturalMap := by
  induction T with
  | zero A =>
    intro a b h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  | @step n m l A U T tail ih =>
    intro a b hab
    have hval := congrArg (fun z : PresentedSet.univ (pointSpace ((p+n)+1) l) S => z.val) hab
    have hhead := congrArg (fun p : Point (M := M) ((p+n)+1) l => vfAt p 0) hval
    have htail := congrArg (dropHead (n := p+n) (id : Fin l → Fin l)) hval
    rw [naturalMap_step,naturalMap_step,dropHead_insertHead,dropHead_insertHead] at htail
    have hContract := ih (Subtype.ext htail)
    have hPair := (T.contractionMap_eq_iff a b).mp hContract
    apply T.bijective.1
    apply Subtype.ext
    refine Prod.ext ?_ ((sameRV_iff _ _).mp hPair.2).2
    funext j
    cases j using Fin.cases with
    | zero => exact hhead
    | succ j => exact hPair.1 j


theorem toMap_frozen (T : PartialContractionProgram S p (n := n) A U) (a : A) (j : Fin p) :
    vfAt (T.toMap a).val j = vfAt a.val (frozenIndex p n j) := by
  induction T with
  | zero A => rfl
  | step T tail ih =>
    exact (ih (T.contractionMap a)).trans (T.contractionMap_vf a _)

theorem naturalMap_frozen (T : PartialContractionProgram S p (n := n) A U) (a : A) (j : Fin p) :
    vfAt (T.naturalMap a).val (frozenIndex p n j) = vfAt a.val (frozenIndex p n j) := by
  induction T with
  | zero A => rfl
  | step T tail ih =>
    exact (ih (T.contractionMap a)).trans (T.contractionMap_vf a _)


end PartialContractionProgram
end IntegrationInACVF.Section5
