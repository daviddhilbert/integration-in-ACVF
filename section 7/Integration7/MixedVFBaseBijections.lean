module

public import Integration7.SelectedVolumeFamilies
public import Section4.ProductBijections
public import Section4.DefinableCategory

@[expose] public section

/-! A definable VF base bijection acts on a mixed family by changing
only its VF tuple. Its actual image retains the finite selected RV fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a k : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) S}

def mixedVFBaseMap (φ : Map X Y) (U : DefSet (rawMixedSpace (M := M) n a) S)
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) :
    Map U (DefSet.univ (rawMixedSpace (M := M) n a) S) := by
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  let i : Map U (X.prod R) := Map.inclusion (fun p hp => ⟨hU ⟨p,hp⟩,Set.mem_univ _⟩)
  exact ((Map.prodMap φ (Map.id R)).comp i).toUniv

theorem mixed_vf_base_map_value (φ : Map X Y) (U : DefSet (rawMixedSpace (M := M) n a) S)
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) (p : U) :
    (mixedVFBaseMap φ U hU p).val = ((φ ⟨p.val.1,hU p⟩).val,p.val.2) := rfl

theorem mixed_vf_base_map_injective (φ : Map X Y) (hφ : Function.Injective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) S) (hU : ∀ p : U, p.val.1 ∈ X.carrier) :
    Function.Injective (mixedVFBaseMap φ U hU) := by
  intro p q h
  have hv := congrArg Subtype.val h
  change ((φ ⟨p.val.1,hU p⟩).val,p.val.2) = ((φ ⟨q.val.1,hU q⟩).val,q.val.2) at hv
  have hx : p.val.1 = q.val.1 := congrArg Subtype.val
    (hφ (Subtype.ext (congrArg Prod.fst hv)))
  have hr := congrArg (fun z : (Fin n → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M) => z.2) hv
  exact Subtype.ext (Prod.ext hx hr)

theorem mixed_vf_base_map_to_image_bijective (φ : Map X Y) (hφ : Function.Injective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) S) (hU : ∀ p : U, p.val.1 ∈ X.carrier) :
    Function.Bijective (mixedVFBaseMap φ U hU).toImage := by
  constructor
  · intro p q h
    have he : mixedVFBaseMap φ U hU p = mixedVFBaseMap φ U hU q :=
      Subtype.ext (congrArg (fun z : (mixedVFBaseMap φ U hU).image => z.val) h)
    exact mixed_vf_base_map_injective φ hφ U hU he
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

theorem mixed_vf_base_image_finite_selected (φ : Map X Y) (hφ : Function.Bijective φ)
    (U : DefSet (rawMixedSpace (M := M) n a) S) (hU : ∀ p : U, p.val.1 ∈ X.carrier)
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VFType (M := M)) (t : Fin k → CanonicalRV.RVSort M),
      {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ U.carrier ∧ r ∘ ρ = t}.Finite)
    (y : Fin n → VFType (M := M)) (t : Fin k → CanonicalRV.RVSort M) :
    {r : Fin a → CanonicalRV.RVSort M | (y,r) ∈ (mixedVFBaseMap φ U hU).image.carrier ∧ r ∘ ρ = t}.Finite := by
  by_cases hy : y ∈ Y.carrier
  · let x := φ.inverse hφ ⟨y,hy⟩
    apply (hfin x.val t).subset
    rintro r ⟨⟨p,hp⟩,ht⟩
    have hBase : (φ ⟨p.val.1,hU p⟩).val = y := congrArg Prod.fst hp
    have hx : p.val.1 = x.val := congrArg Subtype.val
      (hφ.1 (Subtype.ext (hBase.trans (congrArg Subtype.val (Map.apply_inverse φ hφ ⟨y,hy⟩)).symm)))
    have hr : p.val.2 = r := congrArg Prod.snd hp
    refine ⟨?_,ht⟩
    have he : p.val = (x.val,r) := Prod.ext hx hr
    exact he ▸ p.property
  · apply Set.finite_empty.subset
    rintro r ⟨⟨p,hp⟩,ht⟩
    have hBase : (φ ⟨p.val.1,hU p⟩).val = y := congrArg Prod.fst hp
    exact hy (hBase ▸ (φ ⟨p.val.1,hU p⟩).property)

end IntegrationInACVF.Section7
