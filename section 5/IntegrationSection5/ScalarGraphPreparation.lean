import IntegrationSection5.GammaPartialContraction
import IntegrationSection5.PartialNaturalImage
import IntegrationSection5.PartialNaturalCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {p m : ℕ}

def scalarGraphInsert (x : Point (M := M) (p+1) m) (y : Point (M := M) 1 0) :
    Point (M := M) (p+2) m :=
  insertHead (vfAt x 0) (insertHead (vfAt y 0) (dropHead id x))

def scalarGraphInsertMap (A : DefSet (M := M) S (p+1) m) :
    Map (PresentedSet.prod A (PresentedSet.univ (pointSpace 1 0) S))
      (PresentedSet.univ (pointSpace (p+2) m) S) :=
  Map.ofCodes _ (fun q => scalarGraphInsert q.1 q.2)
    (fun z => Sum.elim
      (Fin.cases (z (.inl (.inl 0)))
        (Fin.cases (z (.inr (.inl 0))) (fun j => z (.inl (.inl j.succ)))))
      (fun j => z (.inl (.inr j))))
    (by
      intro j
      cases j with
      | inl j =>
        cases j using Fin.cases with
        | zero => exact rawProj S (.inl (.inl 0) : (Fin (p+1) ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0))
        | succ j =>
          cases j using Fin.cases with
          | zero => exact rawProj S (.inr (.inl 0) : (Fin (p+1) ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0))
          | succ j => exact rawProj S (.inl (.inl j.succ) : (Fin (p+1) ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0))
      | inr j => exact rawProj S (.inl (.inr j) : (Fin (p+1) ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin 0)))
    (by
      intro c
      refine ⟨?_,c.property.1.2⟩
      intro j
      cases j using Fin.cases with
      | zero => exact c.property.1.1 0
      | succ j =>
        cases j using Fin.cases with
        | zero => exact c.property.2.1 0
        | succ j => exact c.property.1.1 j.succ)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => cases j using Fin.cases <;> rfl)

def deleteSecond (q : Point (M := M) (p+2) m) : Point (M := M) (p+1) m :=
  insertHead (vfAt q 0) (dropHead id (dropHead id q))

def deleteSecondMap (A : DefSet (M := M) S (p+2) m) :
    Map A (PresentedSet.univ (pointSpace (p+1) m) S) :=
  Map.ofCodes A deleteSecond
    (fun z => Sum.elim (Fin.cases (z (.inl 0)) (fun j => z (.inl j.succ.succ))) (fun j => z (.inr j)))
    (by intro j; cases j with
        | inl j => cases j using Fin.cases <;> exact rawProj S _
        | inr j => exact rawProj S _)
    (by intro c; refine ⟨?_,c.property.2⟩
        intro j; cases j using Fin.cases with
        | zero => exact c.property.1 0
        | succ j => exact c.property.1 j.succ.succ)
    (by intro c; refine Prod.ext ?_ rfl
        funext j; cases j using Fin.cases <;> rfl)

def secondHeadPointMap (A : DefSet (M := M) S (p+2) m) :
    Map A (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.comp (headPointMap (PresentedSet.univ (pointSpace (p+1) m) S)) (dropHeadMap id A)

theorem deleteSecond_scalarGraphInsert (x : Point (M := M) (p+1) m) (y : Point (M := M) 1 0) :
    deleteSecond (scalarGraphInsert x y) = x := by
  refine Prod.ext ?_ rfl
  funext j
  cases j using Fin.cases <;> rfl

theorem scalarGraphInsert_reconstruct (q : Point (M := M) (p+2) m) :
    scalarGraphInsert (deleteSecond q) (![vfAt q 1],Fin.elim0) = q := by
  refine Prod.ext ?_ rfl
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases <;> rfl

def scalarGraphMap (A : DefSet (M := M) S (p+1) m)
    (f : Map A (PresentedSet.univ (pointSpace 1 0) S)) :
    Map A (PresentedSet.univ (pointSpace (p+2) m) S) :=
  Map.comp (scalarGraphInsertMap A) (Map.pair (Map.id A) f)

theorem scalarGraphMap_injective (A : DefSet (M := M) S (p+1) m)
    (f : Map A (PresentedSet.univ (pointSpace 1 0) S)) : Function.Injective (scalarGraphMap A f) := by
  intro a b hab
  have h := congrArg (fun q : PresentedSet.univ (pointSpace (M := M) (p+2) m) S => deleteSecond q.val) hab
  change deleteSecond (scalarGraphInsert a.val (f a).val) = deleteSecond (scalarGraphInsert b.val (f b).val) at h
  rw [deleteSecond_scalarGraphInsert,deleteSecond_scalarGraphInsert] at h
  exact Subtype.ext h



theorem secondHead_scalarGraphInsert (x : Point (M := M) (p+1) m) (y : Point (M := M) 1 0) :
    (secondHeadPointMap (PresentedSet.univ (pointSpace (M := M) (p+2) m) S)
      ⟨scalarGraphInsert x y,Set.mem_univ _⟩).val = y := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext j
  fin_cases j
  rfl

theorem gamma_scalarGraphMap_graph {P : GammaParameters.Base (M := M)}
    (A : DefSet (M := M) S (p+1) m) (hA : GammaSetDefinable P (carrier A))
    (f : Map A (PresentedSet.univ (pointSpace 1 0) S))
    (hf : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P (pointMapGraph (scalarGraphMap A f)) := by
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) (p+1) m) P.real)
  let D := deleteSecondMap (PresentedSet.univ (pointSpace (M := M) (p+2) m) P.real)
  let H := secondHeadPointMap (PresentedSet.univ (pointSpace (M := M) (p+2) m) P.real)
  have h := ((gamma_identity_graph A hA).preimage_maps I D).inter (hf.preimage_maps I H)
  apply GammaGraphDefinable.congr h
  intro x y
  constructor
  · rintro ⟨⟨a,ha,hD⟩,⟨b,hb,hH⟩⟩
    have he : b = a := Subtype.ext (hb.trans ha.symm)
    subst b
    refine ⟨a,ha,?_⟩
    change scalarGraphInsert a.val (f a).val = y
    change a.val = deleteSecond y at hD
    rw [hD,hH]
    exact scalarGraphInsert_reconstruct y
  · rintro ⟨a,rfl,he⟩
    refine ⟨⟨a,rfl,?_⟩,⟨a,rfl,?_⟩⟩
    · exact (deleteSecond_scalarGraphInsert a.val (f a).val).symm.trans (congrArg deleteSecond he)
    · exact (secondHead_scalarGraphInsert (S := P.real) a.val (f a).val).symm.trans
        (congrArg (fun q : Point (M := M) (p+2) m => (H ⟨q,Set.mem_univ _⟩).val) he)

end IntegrationInACVF.Section5
