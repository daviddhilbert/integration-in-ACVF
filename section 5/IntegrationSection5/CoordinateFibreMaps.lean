import IntegrationSection5.RelativeFibreGeometry
import Section5.ParameterExtension

/-! Definable insertion and projection maps for actual one-coordinate
fibres, over the original real base augmented by the other VF coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

local notation "N" => (@CanonicalStructure.normalize M sM)

def coordinateInsertMap (S : Set M) (i : Fin n) (u : Fin n → VF (M := M)) :
    Map (PresentedSet.univ (pointSpace (M := M) 1 m) (coordinateFibreBase S i u))
      (PresentedSet.univ (pointSpace n m) (coordinateFibreBase S i u)) :=
  let R := coordinateFibreBase S i u
  Map.ofCodes _ (coordinateInsert i u)
    (fun z => Sum.elim (fun j => if j = i then z (.inl 0) else (u j).val)
      (fun j => z (.inr j)))
    (by
      intro j
      cases j with
      | inl j =>
        by_cases hj : j = i
        · simpa only [Sum.elim_inl,hj,ite_true] using rawProj R (.inl 0 : Fin 1 ⊕ Fin m)
        · have hmem : (u j).val ∈ R := Or.inr ⟨⟨j,hj⟩,rfl⟩
          have hd : RawFun R (Fin 1 ⊕ Fin m) (fun _ => (u j).val) := by
            letI := N
            exact LRV.definableFun_const _ hmem
          simpa only [Sum.elim_inl,hj,ite_false] using hd
      | inr j => exact rawProj R (.inr j : Fin 1 ⊕ Fin m))
    (by
      intro c
      refine ⟨?_,c.property.2⟩
      intro j
      by_cases hj : j = i
      · simpa only [hj,ite_true,Function.comp_apply,Sum.elim_inl,sortEval,iVF] using c.property.1 0
      · simpa only [hj,ite_false,Function.comp_apply,Sum.elim_inl,sortEval,iVF] using (u j).property)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext j
      apply Subtype.ext
      by_cases hj : j = i
      · subst j
        simp [coordinateInsert,vfAt,Function.update_self,Function.comp_def]
      · simp [coordinateInsert,Function.update_of_ne hj,Function.comp_def,hj])

def coordinateProjectMap (i : Fin n) (A : DefSet (M := M) S n m) :
    Map A (PresentedSet.univ (pointSpace 1 m) S) :=
  Map.ofCodes A (coordinateProject i)
    (fun z => Sum.elim (fun _ => z (.inl i)) (fun j => z (.inr j)))
    (by
      intro j
      cases j with
      | inl j => exact rawProj S (.inl i : Fin n ⊕ Fin m)
      | inr j => exact rawProj S (.inr j : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun _ => c.property.1 i,c.property.2⟩)
    (by intro c; rfl)

def coordinateFibre (A : DefSet (M := M) S n m) (i : Fin n) (u : Fin n → VF (M := M)) :
    DefSet (M := M) (coordinateFibreBase S i u) 1 m :=
  let hA := SetDefinable.mono (pointSpace n m) (setDefinable A) (Set.subset_union_left : S ⊆ coordinateFibreBase S i u)
  PresentedSet.mk {p | coordinateInsert i u p ∈ carrier A} (by
    have hd := Map.definable_preimage (coordinateInsertMap S i u) hA
    convert hd using 1
    ext p
    constructor
    · intro hp; exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
    · rintro ⟨a,rfl,ha⟩; exact ha)

def mapIntoSubset {X Y : PresentedSpace (M := M)} {A : PresentedSet X S} {C : PresentedSet Y S}
    (f : Map A C) (D : PresentedSet Y S) (h : ∀ a : A, (f a).val ∈ carrier D) : Map A D :=
  Map.mk (fun a => ⟨(f a).val,h a⟩) (Map.graph_definable f)

def coordinateFibreEmbedding (A : DefSet (M := M) S n m) (i : Fin n)
    (u : Fin n → VF (M := M)) :
    Map (coordinateFibre A i u) (extendBase A (Set.subset_union_left : S ⊆ coordinateFibreBase S i u)) :=
  let g := Map.comp (coordinateInsertMap S i u)
    (Map.inclusion (Set.subset_univ _) : Map (coordinateFibre A i u)
      (PresentedSet.univ (pointSpace 1 m) (coordinateFibreBase S i u)))
  mapIntoSubset g _ (fun a => a.property)

theorem coordinateFibreEmbedding_apply (A : DefSet (M := M) S n m) (i : Fin n)
    (u : Fin n → VF (M := M)) (a : coordinateFibre A i u) :
    (coordinateFibreEmbedding A i u a).val = coordinateInsert i u a.val := rfl

end IntegrationInACVF.Section5
