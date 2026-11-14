import Integration7.VolumeForms
import Integration7.RVCoordinateSelection
import Section4.MapParameters
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p a : ℕ}

def mixedInsertVFTuple (S : Set M) (x : Fin p → VFType (M := M)) (a : ℕ) :
    Map (DefSet.univ (rawRVSpace (M := M) a) (S ∪ Set.range (fun i => (x i).val)))
      (DefSet.univ (rawMixedSpace (M := M) p a) (S ∪ Set.range (fun i => (x i).val))) := by
  let F (z : Fin a → M) : Fin p ⊕ Fin a → M := Sum.elim (fun i => (x i).val) z
  have hcode (c : (rawRVSpace (M := M) a).domain) :
      mixedValues (x,(rawRVSpace (M := M) a).decode c)=F c.val := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact congrFun (rvValues_decode c) i
  refine Map.ofCodes _ (fun r => (x,r)) F ?_
    (fun c => (hcode c) ▸ mixedValues_mem_domain (x,(rawRVSpace (M := M) a).decode c)) ?_
  · intro i
    cases i with
    | inl i => exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    | inr i => exact Set.DefinableFun.proj LRV
  · intro c
    exact mixedValues_injective ((mixedValues_decode _).trans (hcode c).symm)

def vfRVFibre (A : DefSet (rawMixedSpace (M := M) p a) S) (x : Fin p → VFType (M := M)) :
    DefSet (rawRVSpace (M := M) a) (S ∪ Set.range (fun i => (x i).val)) where
  carrier := {r | (x,r) ∈ A.carrier}
  definable := by
    have h := (mixedInsertVFTuple S x a).definable_preimage (A.definable.mono _ Set.subset_union_left)
    convert h using 1
    ext r
    constructor
    · intro hr
      exact ⟨⟨r,Set.mem_univ _⟩,rfl,hr⟩
    · rintro ⟨r',rfl,hr⟩
      exact hr

def vfRVFibreEmbed (A : DefSet (rawMixedSpace (M := M) p a) S) (x : Fin p → VFType (M := M)) :
    Map (vfRVFibre A x) (A.extend (Set.subset_union_left : S ⊆ S ∪ Set.range (fun i => (x i).val))) where
  toFun r := ⟨(x,r.val),r.property⟩
  graph_definable := ((mixedInsertVFTuple S x a).restrict (A' := vfRVFibre A x) (Set.subset_univ _)).graph_definable

def VolumeForm.vfRVFibre {A : DefSet (rawMixedSpace (M := M) p a) S} (ω : VolumeForm A)
    (x : Fin p → VFType (M := M)) : VolumeForm (vfRVFibre A x) :=
  (ω.extend Set.subset_union_left).pullback (vfRVFibreEmbed A x)

@[simp] theorem VolumeForm.vfRVFibre_value {A : DefSet (rawMixedSpace (M := M) p a) S} (ω : VolumeForm A)
    (x : Fin p → VFType (M := M)) (r : IntegrationInACVF.Section7.vfRVFibre A x) :
    (ω.vfRVFibre x).value r=ω.value ⟨(x,r.val),r.property⟩ := rfl
end IntegrationInACVF.Section7
