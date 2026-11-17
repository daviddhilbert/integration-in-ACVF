module

public import Integration7.DefinableMapPreimages
public import Section4.CoordinateMaps
public import Section4.RVRestrictions
public import Section4.MapCorestrict
public import Section4.CanonicalLift
public import Section4.VFRealFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Selected old RV labels are realized by additional VF tail
coordinates. This turns finiteness at fixed selected labels into actual
finite RV fibres, without adjoining parameters to the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def selectedRVVFTailConstraint (S : Set M) (n : ℕ) {a d : ℕ} (ρ : Fin d → Fin a) :
    DefSet (rawMixedSpace (M := M) (n+d) a) S where
  carrier := {p | tupleRV (p.1 ∘ Fin.natAdd n) = p.2 ∘ ρ}
  definable := by
    let P := rawMixedSpace (M := M) (n+d) a
    have hEq : S.Definable LRV {z : Fin (n+d) ⊕ Fin a → M |
        ∀ j, iRv (z (.inl (Fin.natAdd n j))) = z (.inr (ρ j))} := by
      simp only [Set.ofPred_forall]
      apply Set.definable_iInter_of_finite
      intro j
      have hRv : S.DefinableFun LRV (fun z : Fin (n+d) ⊕ Fin a → M =>
          iRv (z (.inl (Fin.natAdd n j)))) :=
        (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
          (show S.DefinableMap LRV (fun z : Fin (n+d) ⊕ Fin a → M =>
            ![z (.inl (Fin.natAdd n j))]) from
              fun t => by fin_cases t; exact Set.DefinableFun.proj LRV)
      exact hRv.ofPred_eq (Set.DefinableFun.proj LRV)
    have hDecode (c : P.domain) :
        tupleRV ((P.decode c).1 ∘ Fin.natAdd n) = (P.decode c).2 ∘ ρ ↔
          ∀ j, iRv (c.val (.inl (Fin.natAdd n j))) = c.val (.inr (ρ j)) := by
      rw [funext_iff]
      apply forall_congr'
      intro j
      have hx := congrFun (mixedValues_decode c) (.inl (Fin.natAdd n j))
      have hr := congrFun (mixedValues_decode c) (.inr (ρ j))
      change ((P.decode c).1 (Fin.natAdd n j)).val = _ at hx
      change ((P.decode c).2 (ρ j)).val = _ at hr
      constructor
      · intro h
        have hv := congrArg Subtype.val h
        change iRv (((P.decode c).1 (Fin.natAdd n j)).val) = ((P.decode c).2 (ρ j)).val at hv
        rwa [hx,hr] at hv
      · intro h
        apply Subtype.ext
        change iRv (((P.decode c).1 (Fin.natAdd n j)).val) = ((P.decode c).2 (ρ j)).val
        rwa [hx,hr]
    change S.Definable LRV {z | ∃ hz : z ∈ P.domain,
      tupleRV ((P.decode ⟨z,hz⟩).1 ∘ Fin.natAdd n) = (P.decode ⟨z,hz⟩).2 ∘ ρ}
    convert (P.definable_domain S).inter hEq using 1
    ext z
    exact ⟨fun ⟨hz,h⟩ => ⟨hz,(hDecode ⟨z,hz⟩).mp h⟩,
      fun ⟨hz,h⟩ => ⟨hz,(hDecode ⟨z,hz⟩).mpr h⟩⟩

def selectedRVVFTailLift (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a) :
    DefSet (rawMixedSpace (M := M) (n+d) a) S :=
  (definableMapPreimage (vfSelect (Fin.castAdd d) (DefSet.univ (rawMixedSpace (n+d) a) S)) A).inter
    (selectedRVVFTailConstraint S n ρ)

theorem mem_selected_rv_vf_tail_lift
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a)
    (p : (Fin (n+d) → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M)) :
    p ∈ (selectedRVVFTailLift A ρ).carrier ↔
      (p.1 ∘ Fin.castAdd d,p.2) ∈ A.carrier ∧ tupleRV (p.1 ∘ Fin.natAdd n) = p.2 ∘ ρ :=
  and_congr (mem_definableMapPreimage
    (vfSelect (Fin.castAdd d) (DefSet.univ (rawMixedSpace (M := M) (n+d) a) S)) A
    (⟨p,Set.mem_univ _⟩ : DefSet.univ (rawMixedSpace (M := M) (n+d) a) S)) Iff.rfl

theorem selected_rv_vf_tail_lift_finite_labels
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin d → CanonicalRV.RVSort M),
      {r | (x,r) ∈ A.carrier ∧ r ∘ ρ = t}.Finite)
    (x : Fin (n+d) → VFType (M := M)) :
    {r | (x,r) ∈ (selectedRVVFTailLift A ρ).carrier}.Finite := by
  apply (hfin (x ∘ Fin.castAdd d) (tupleRV (x ∘ Fin.natAdd n))).subset
  intro r hr
  have h := (mem_selected_rv_vf_tail_lift A ρ (x,r)).mp hr
  exact ⟨h.1,h.2.symm⟩

def selectedRVVFTailProjection
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a) :
    Map (selectedRVVFTailLift A ρ) A :=
  (vfSelect (Fin.castAdd d) (selectedRVVFTailLift A ρ)).corestrict
    (fun p => ((mem_selected_rv_vf_tail_lift A ρ p.val).mp p.property).1)

theorem selected_rv_vf_tail_projection_surjective
    (A : DefSet (rawMixedSpace (M := M) n a) S) (ρ : Fin d → Fin a) :
    Function.Surjective (selectedRVVFTailProjection A ρ) := by
  intro p
  obtain ⟨y,hy⟩ := tupleRV_surjective (p.val.2 ∘ ρ)
  have hx : (Fin.append p.val.1 y) ∘ Fin.castAdd d = p.val.1 :=
    funext (Fin.append_left _ _)
  have ht : (Fin.append p.val.1 y) ∘ Fin.natAdd n = y :=
    funext (Fin.append_right _ _)
  have hp : (Fin.append p.val.1 y,p.val.2) ∈ (selectedRVVFTailLift A ρ).carrier := by
    rw [mem_selected_rv_vf_tail_lift,hx,ht]
    exact ⟨p.property,hy⟩
  refine ⟨⟨(Fin.append p.val.1 y,p.val.2),hp⟩,?_⟩
  exact Subtype.ext (Prod.ext hx rfl)

end IntegrationInACVF.Section7
