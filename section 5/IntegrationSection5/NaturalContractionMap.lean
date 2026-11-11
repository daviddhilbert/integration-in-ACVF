import IntegrationSection5.OrderedContractionProgram

/-! The actual definable natural lift map of an ordered contraction
program, with all VF coordinates and retained RV labels explicit. -/
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
variable {S : Set M} {n m l : ℕ}

def firstVFMap (A : DefSet (M := M) S (n+1) m) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.ofCodes A (fun p => ![vfAt p 0]) (fun z _ => z (.inl 0))
    (fun _ => rawProj S (.inl 0 : Fin (n+1) ⊕ Fin m))
    (fun c _ => c.property.1 0) (by
      intro c
      funext j
      fin_cases j
      apply Subtype.ext
      rfl)

def insertHeadMap (S : Set M) (n l : ℕ) :
    Map (PresentedSet.prod (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)
      (PresentedSet.univ (pointSpace n l) S)) (PresentedSet.univ (pointSpace (n+1) l) S) :=
  Map.ofCodes _ (fun p => insertHead (p.1 0) p.2)
    (fun z => Sum.elim (Fin.cases (z (.inl 0)) (fun j => z (.inr (.inl j)))) (fun j => z (.inr (.inr j))))
    (by
      intro j
      cases j with
      | inl j =>
        cases j using Fin.cases with
        | zero => exact rawProj S (.inl 0 : Fin 1 ⊕ (Fin n ⊕ Fin l))
        | succ j => exact rawProj S (.inr (.inl j) : Fin 1 ⊕ (Fin n ⊕ Fin l))
      | inr j => exact rawProj S (.inr (.inr j) : Fin 1 ⊕ (Fin n ⊕ Fin l)))
    (by
      intro c
      refine ⟨?_,c.property.2.2⟩
      intro j
      cases j using Fin.cases with
      | zero => exact c.property.1 0
      | succ j => exact c.property.2.1 j)
    (by
      intro c
      refine Prod.ext ?_ ?_
      · funext j
        cases j using Fin.cases <;> apply Subtype.ext <;> rfl
      · funext j
        apply Subtype.ext
        rfl)

namespace OrderedContractionProgram
variable {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}

def naturalMap {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c} :
    OrderedContractionProgram S X Y → Map X (PresentedSet.univ (pointSpace a c) S)
  | .zero A => Map.inclusion (Set.subset_univ _)
  | .step T tail =>
    Map.comp (insertHeadMap S _ _)
      (Map.pair (Map.comp (firstVFMap T.target) T.map) (Map.comp tail.naturalMap T.contractionMap))

theorem naturalMap_zero {A : DefSet (M := M) S 0 m} (a : A) :
    ((zero A).naturalMap a).val = a.val := rfl

theorem naturalMap_step {a b c : ℕ} {X : DefSet (M := M) S (a+1) b} {Y : DefSet (M := M) S 0 c}
    (T : HeadPreparation X) (tail : OrderedContractionProgram S T.contractedSet Y) (x : X) :
    ((step T tail).naturalMap x).val =
      insertHead (vfAt (T.map x).val 0) (tail.naturalMap (T.contractionMap x)).val := rfl

theorem naturalMap_labels (T : OrderedContractionProgram S A U) (a : A) :
    (T.naturalMap a).val.2 = (T.toMap a).val.2 := by
  induction T with
  | zero A => rfl
  | step T tail ih => exact ih (T.contractionMap a)

theorem naturalMap_rv (T : OrderedContractionProgram S A U) (a : A) (i : Fin n) :
    (T.toMap a).val.2 (T.volumeIndex i) = rv (vfAt (T.naturalMap a).val i) := by
  induction T with
  | zero A => exact Fin.elim0 i
  | @step n m l A U T tail ih =>
    cases i using Fin.cases with
    | zero =>
      have h := tail.oldLabels (T.contractionMap a) (0 : Fin (1+T.arity))
      refine h.trans ?_
      have hk := congrArg (fun p : Point (M := M) n (1+T.arity) => p.2 (Fin.castAdd T.arity 0))
        (headKeyMap_apply T.target (T.map a))
      exact hk
    | succ i => exact ih (T.contractionMap a) i

theorem naturalMap_injective (T : OrderedContractionProgram S A U) : Function.Injective T.naturalMap := by
  induction T with
  | zero A =>
    intro a b h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  | @step n m l A U T tail ih =>
    intro a b hab
    have hval := congrArg (fun z : PresentedSet.univ (pointSpace (n+1) l) S => z.val) hab
    have hhead := congrArg (fun p : Point (M := M) (n+1) l => vfAt p 0) hval
    have htail := congrArg (dropHead (n := n) (id : Fin l → Fin l)) hval
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

end OrderedContractionProgram
end IntegrationInACVF.Section5
