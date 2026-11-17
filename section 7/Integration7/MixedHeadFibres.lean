module

public import Integration7.VFRVFibres
public import Integration7.FiniteVolumeParameterContexts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual unary head fibres of raw mixed definable sets, with the
literal frozen VF parameters and the original nonzero density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

def mixedHeadInsert (S : Set M) (x : Fin n → VFType (M := M)) (a : ℕ) :
    Map (DefSet.univ (rawMixedSpace (M := M) 1 a) (S ∪ Set.range (fun i => (x i).val)))
      (DefSet.univ (rawMixedSpace (M := M) (n+1) a) (S ∪ Set.range (fun i => (x i).val))) := by
  let F (z : Fin 1 ⊕ Fin a → M) : Fin (n+1) ⊕ Fin a → M :=
    Sum.elim (Fin.cons (z (.inl 0)) (fun i => (x i).val)) (fun i => z (.inr i))
  have hcode (c : (rawMixedSpace (M := M) 1 a).domain) :
      mixedValues (Fin.cons (((rawMixedSpace (M := M) 1 a).decode c).1 0) x,
        ((rawMixedSpace (M := M) 1 a).decode c).2) = F c.val := by
    have h := mixedValues_decode c
    funext i
    cases i with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrFun h (.inl 0)
      · rfl
    | inr i => exact congrFun h (.inr i)
  refine Map.ofCodes _ (fun p => (Fin.cons (p.1 0) x,p.2)) F ?_
    (fun c => hcode c ▸ mixedValues_mem_domain _) ?_
  · intro i
    cases i with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
    | inr i => exact Set.DefinableFun.proj LRV
  · intro c
    exact mixedValues_injective ((mixedValues_decode _).trans (hcode c).symm)

def mixedHeadFibre (A : DefSet (rawMixedSpace (M := M) (n+1) a) S)
    (x : Fin n → VFType (M := M)) :
    DefSet (rawMixedSpace (M := M) 1 a) (S ∪ Set.range (fun i => (x i).val)) where
  carrier := {p | (Fin.cons (p.1 0) x,p.2) ∈ A.carrier}
  definable := by
    have h := (mixedHeadInsert S x a).definable_preimage (A.definable.mono _ Set.subset_union_left)
    convert h using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
    · rintro ⟨p,rfl,hp⟩
      exact hp

def mixedHeadFibreEmbed (A : DefSet (rawMixedSpace (M := M) (n+1) a) S)
    (x : Fin n → VFType (M := M)) :
    Map (mixedHeadFibre A x) (A.extend (Set.subset_union_left : S ⊆ S ∪ Set.range (fun i => (x i).val))) where
  toFun p := ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩
  graph_definable := ((mixedHeadInsert S x a).restrict (A' := mixedHeadFibre A x) (Set.subset_univ _)).graph_definable

def VolumeForm.mixedHeadFibre {A : DefSet (rawMixedSpace (M := M) (n+1) a) S}
    (ω : VolumeForm A) (x : Fin n → VFType (M := M)) : VolumeForm (IntegrationInACVF.Section7.mixedHeadFibre A x) :=
  (ω.extend Set.subset_union_left).pullback (mixedHeadFibreEmbed A x)

@[simp] theorem VolumeForm.mixedHeadFibre_value {A : DefSet (rawMixedSpace (M := M) (n+1) a) S}
    (ω : VolumeForm A) (x : Fin n → VFType (M := M)) (p : IntegrationInACVF.Section7.mixedHeadFibre A x) :
    (ω.mixedHeadFibre x).value p = ω.value ⟨(Fin.cons (p.val.1 0) x,p.val.2),p.property⟩ := rfl

end IntegrationInACVF.Section7
