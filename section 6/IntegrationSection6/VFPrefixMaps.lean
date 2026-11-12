import IntegrationSection6.VFPrefixCoordinates
import IntegrationSection5.CoordinateFibreMaps

/-! Definable insertion and projection of a VF prefix with a frozen tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n p m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def vfPrefixInsertMap (S : Set M) (x : Fin n → VF (M := M)) (p m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p m) (S ∪ Set.range (fun j => (x j).val)))
      (PresentedSet.univ (pointSpace (n+p) m) (S ∪ Set.range (fun j => (x j).val))) :=
  let R := S ∪ Set.range (fun j => (x j).val)
  Map.ofCodes _ (vfPrefixInsert x)
    (fun z => Sum.elim (fun j : Fin (n+p) => if h : j.val < p then z (.inl ⟨j.val,h⟩)
      else (x ⟨j.val-p,by omega⟩).val) (fun j => z (.inr j)))
    (by
      intro j
      cases j with
      | inl j =>
        by_cases hj : j.val < p
        · simpa only [Sum.elim_inl,dite_eq_left hj] using rawProj R (.inl ⟨j.val,hj⟩ : Fin p ⊕ Fin m)
        · have hd : RawFun R (Fin p ⊕ Fin m) (fun _ => (x ⟨j.val-p,by omega⟩).val) := by
            letI := N
            exact LRV.definableFun_const _ (Or.inr ⟨⟨j.val-p,by omega⟩,rfl⟩)
          simpa only [Sum.elim_inl,dite_eq_right hj] using hd
      | inr j => exact rawProj R (.inr j : Fin p ⊕ Fin m))
    (by
      intro c
      refine ⟨?_,c.property.2⟩
      intro j
      by_cases hj : j.val < p
      · simpa only [Function.comp_apply,Sum.elim_inl,dite_eq_left hj] using c.property.1 ⟨j.val,hj⟩
      · simpa only [Function.comp_apply,Sum.elim_inl,dite_eq_right hj,sortEval,iVF] using (x ⟨j.val-p,by omega⟩).property)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext j
      apply Subtype.ext
      by_cases hj : j.val < p
      · simp only [vfPrefixInsert,vfPrefixTuple,Function.comp_apply,Sum.elim_inl,dite_eq_left hj]
      · simp only [vfPrefixInsert,vfPrefixTuple,Function.comp_apply,Sum.elim_inl,dite_eq_right hj])

def vfPrefixProjectMap (A : DefSet (M := M) S (n+p) m) :
    Map A (PresentedSet.univ (pointSpace p m) S) :=
  Map.ofCodes A vfPrefixProject
    (fun z => Sum.elim (fun j : Fin p => z (.inl ⟨j.val,by omega⟩)) (fun j => z (.inr j)))
    (by
      intro j
      cases j with
      | inl j => exact rawProj S (.inl ⟨j.val,by omega⟩ : Fin (n+p) ⊕ Fin m)
      | inr j => exact rawProj S (.inr j : Fin (n+p) ⊕ Fin m))
    (by intro c; exact ⟨fun j => c.property.1 ⟨j.val,by omega⟩,c.property.2⟩)
    (by intro c; rfl)

def vfPrefixFibre (A : DefSet (M := M) S (n+p) m) (x : Fin n → VF (M := M)) :
    DefSet (M := M) (S ∪ Set.range (fun j => (x j).val)) p m :=
  PresentedSet.mk {q | vfPrefixInsert x q ∈ carrier A} (by
    have hA := SetDefinable.mono (pointSpace (n+p) m) (setDefinable A)
      (Set.subset_union_left : S ⊆ S ∪ Set.range (fun j => (x j).val))
    have h := Map.definable_preimage (vfPrefixInsertMap S x p m) hA
    convert h using 1
    ext q
    constructor
    · intro hq
      exact ⟨⟨q,Set.mem_univ _⟩,rfl,hq⟩
    · rintro ⟨a,ha,hax⟩
      exact ha ▸ hax)

def vfPrefixFibreEmbedding (A : DefSet (M := M) S (n+p) m) (x : Fin n → VF (M := M)) :
    Map (vfPrefixFibre A x)
      (extendBase A (Set.subset_union_left : S ⊆ S ∪ Set.range (fun j => (x j).val))) :=
  mapIntoSubset (Map.comp (vfPrefixInsertMap S x p m)
    (Map.inclusion (Set.subset_univ _) : Map (vfPrefixFibre A x)
      (PresentedSet.univ (pointSpace p m) (S ∪ Set.range (fun j => (x j).val))))) _ (fun q => q.property)

end IntegrationInACVF.Section6
