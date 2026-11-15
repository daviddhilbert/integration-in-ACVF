import Integration7.SelectedRVVFTailLifts
import Integration7.MixedDomainProductJacobians

/-! A label-preserving mixed map lifts while fixing the additional VF
coordinates realizing the selected RV tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}

def selectedTailProductInclusion (A : DefSet (rawMixedSpace (M := M) n a) S)
    (ρ : Fin d → Fin a) : Map (selectedRVVFTailLift A ρ)
      (mixedProductDomain A (DefSet.univ (rawMixedSpace (M := M) d 0) S)) := by
  let R := DefSet.univ (rawMixedSpace (M := M) d 0) S
  have hSub : (selectedRVVFTailLift A ρ).carrier ⊆ (mixedProductDomain A R).carrier := by
    intro p hp
    apply (mem_mixedProductDomain A R p).mpr
    exact ⟨((mem_selected_rv_vf_tail_lift A ρ p).mp hp).1,Set.mem_univ _⟩
  exact Map.inclusion hSub

theorem selected_tail_product_unpack (A : DefSet (rawMixedSpace (M := M) n a) S)
    (ρ : Fin d → Fin a) (p : selectedRVVFTailLift A ρ) :
    mixedUnpack A (DefSet.univ (rawMixedSpace (M := M) d 0) S)
      (selectedTailProductInclusion A ρ p) =
    ⟨((selectedRVVFTailProjection A ρ p).val,(p.val.1 ∘ Fin.natAdd n,Fin.elim0)),
      (selectedRVVFTailProjection A ρ p).property,Set.mem_univ _⟩ := by
  let R := DefSet.univ (rawMixedSpace (M := M) d 0) S
  let q : A.prod R :=
    ⟨((selectedRVVFTailProjection A ρ p).val,(p.val.1 ∘ Fin.natAdd n,Fin.elim0)),
      (selectedRVVFTailProjection A ρ p).property,Set.mem_univ _⟩
  have hq : (mixedPack A R).toImage q = selectedTailProductInclusion A ρ p := by
    apply Subtype.ext
    change (Fin.append (p.val.1 ∘ Fin.castAdd d) (p.val.1 ∘ Fin.natAdd n),
      Fin.append p.val.2 Fin.elim0) = p.val
    refine Prod.ext Fin.append_castAdd_natAdd ?_
    change Fin.append p.val.2 Fin.elim0 = p.val.2
    exact Fin.append_elim0 p.val.2
  rw [← hq,mixedUnpack_pack]

def selectedTailLiftMap
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A B) (hLabels : ∀ p : A, (f p).val.2 = p.val.2) (ρ : Fin d → Fin a) :
    Map (selectedRVVFTailLift A ρ) (selectedRVVFTailLift B ρ) := by
  let R := DefSet.univ (rawMixedSpace (M := M) d 0) S
  let g := (mixedDomainProductMap f (Map.id R)).comp (selectedTailProductInclusion A ρ)
  exact g.corestrict (by
    intro p
    have h := (mem_selected_rv_vf_tail_lift A ρ p.val).mp p.property
    let x := selectedRVVFTailProjection A ρ p
    have hv : (g p).val = (Fin.append (f x).val.1 (p.val.1 ∘ Fin.natAdd n),p.val.2) := by
      change ((mixedPack B R).toImage (Map.prodMap f (Map.id R)
        (mixedUnpack A R (selectedTailProductInclusion A ρ p)))).val = _
      rw [selected_tail_product_unpack]
      refine Prod.ext rfl ?_
      change Fin.append (f x).val.2 Fin.elim0 = p.val.2
      rw [hLabels]
      exact Fin.append_elim0 p.val.2
    apply (mem_selected_rv_vf_tail_lift B ρ (g p).val).mpr
    rw [hv]
    have hLeft : Fin.append (f x).val.1 (p.val.1 ∘ Fin.natAdd n) ∘ Fin.castAdd d = (f x).val.1 :=
      funext (Fin.append_left _ _)
    have hRight : Fin.append (f x).val.1 (p.val.1 ∘ Fin.natAdd n) ∘ Fin.natAdd n = p.val.1 ∘ Fin.natAdd n :=
      funext (Fin.append_right _ _)
    rw [hLeft,hRight]
    exact ⟨(hLabels x) ▸ (f x).property,h.2⟩)

theorem selected_tail_lift_map_value
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A B) (hLabels : ∀ p : A, (f p).val.2 = p.val.2) (ρ : Fin d → Fin a)
    (p : selectedRVVFTailLift A ρ) :
    (selectedTailLiftMap f hLabels ρ p).val =
      (Fin.append (f (selectedRVVFTailProjection A ρ p)).val.1 (p.val.1 ∘ Fin.natAdd n),p.val.2) := by
  change ((mixedPack B (DefSet.univ (rawMixedSpace (M := M) d 0) S)).toImage
    (Map.prodMap f (Map.id _) (mixedUnpack A _ (selectedTailProductInclusion A ρ p)))).val = _
  rw [selected_tail_product_unpack]
  refine Prod.ext rfl ?_
  change Fin.append (f (selectedRVVFTailProjection A ρ p)).val.2 Fin.elim0 = p.val.2
  rw [hLabels]
  exact Fin.append_elim0 p.val.2

theorem selected_tail_lift_map_projection
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A B) (hLabels : ∀ p : A, (f p).val.2 = p.val.2) (ρ : Fin d → Fin a)
    (p : selectedRVVFTailLift A ρ) :
    selectedRVVFTailProjection B ρ (selectedTailLiftMap f hLabels ρ p) =
      f (selectedRVVFTailProjection A ρ p) := by
  apply Subtype.ext
  change ((selectedTailLiftMap f hLabels ρ p).val.1 ∘ Fin.castAdd d,
    (selectedTailLiftMap f hLabels ρ p).val.2) = _
  rw [selected_tail_lift_map_value]
  exact Prod.ext (funext (Fin.append_left _ _)) (hLabels (selectedRVVFTailProjection A ρ p)).symm

theorem selected_tail_lift_map_bijective
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A B) (hf : Function.Bijective f)
    (hLabels : ∀ p : A, (f p).val.2 = p.val.2) (ρ : Fin d → Fin a) :
    Function.Bijective (selectedTailLiftMap f hLabels ρ) := by
  have hInvLabels : ∀ q : B, (f.inverse hf q).val.2 = q.val.2 := by
    intro q
    exact (hLabels (f.inverse hf q)).symm.trans (congrArg (fun z : B => z.val.2) (Map.apply_inverse f hf q))
  let g := selectedTailLiftMap (f.inverse hf) hInvLabels ρ
  have hLeft (p : selectedRVVFTailLift A ρ) : g (selectedTailLiftMap f hLabels ρ p) = p := by
    apply Subtype.ext
    rw [selected_tail_lift_map_value,selected_tail_lift_map_projection,Map.inverse_apply]
    have hTail : (selectedTailLiftMap f hLabels ρ p).val.1 ∘ Fin.natAdd n = p.val.1 ∘ Fin.natAdd n := by
      rw [selected_tail_lift_map_value]
      exact funext (Fin.append_right _ _)
    rw [hTail,selected_tail_lift_map_value]
    exact Prod.ext Fin.append_castAdd_natAdd rfl
  have hRight (q : selectedRVVFTailLift B ρ) : selectedTailLiftMap f hLabels ρ (g q) = q := by
    apply Subtype.ext
    rw [selected_tail_lift_map_value,selected_tail_lift_map_projection,Map.apply_inverse]
    have hTail : (g q).val.1 ∘ Fin.natAdd n = q.val.1 ∘ Fin.natAdd n := by
      change (selectedTailLiftMap (f.inverse hf) hInvLabels ρ q).val.1 ∘ Fin.natAdd n = _
      rw [selected_tail_lift_map_value]
      exact funext (Fin.append_right _ _)
    rw [hTail]
    have hLabelsG : (g q).val.2 = q.val.2 := by
      have h := congrArg
        (fun z : (Fin (n+d) → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M) => z.2)
        (selected_tail_lift_map_value (f.inverse hf) hInvLabels ρ q)
      exact h
    rw [hLabelsG]
    exact Prod.ext Fin.append_castAdd_natAdd rfl
  exact ⟨fun p q h => (hLeft p).symm.trans ((congrArg g h).trans (hLeft q)),fun q => ⟨g q,hRight q⟩⟩

end IntegrationInACVF.Section7
