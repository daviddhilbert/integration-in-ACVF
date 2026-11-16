module

public import Integration7.OrdinaryFiniteCoproductIsomorphisms
public import Integration7.OrdinaryZeroLiftIsomorphisms

@[expose] public section

/-! Ordinary degree-zero lifts commute with the actual tagged VF
coproduct through identity on their literal mixed tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem ordinary_zero_lift_coprod_carrier (U V : RVFiniteObject (M := M) S 0)
    (p : (Fin 0 → VFType (M := M)) × (Fin (1+(U.obj.arity+V.obj.arity)) → CanonicalRV.RVSort M)) :
    p ∈ (rvLift (rvCoprodObject U.obj V.obj)).carrier ↔
      p ∈ (vfAllCoprodObject (rvLiftObject (rawRVSpace (M := M) 1) U.obj).obj
        (rvLiftObject (rawRVSpace (M := M) 1) V.obj).obj).set.carrier := by
  constructor
  · rintro ⟨u,hu,_⟩
    rcases u.property with ⟨v,hv⟩ | ⟨w,hw⟩
    · refine Or.inl ⟨⟨(p.1,v.val),v,rfl,?_⟩,?_⟩
      · funext i; exact i.elim0
      · exact Prod.ext (funext fun i => i.elim0) (hv.trans hu)
    · refine Or.inr ⟨⟨(p.1,w.val),w,rfl,?_⟩,?_⟩
      · funext i; exact i.elim0
      · exact Prod.ext (funext fun i => i.elim0) (hw.trans hu)
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · obtain ⟨r,hr,_⟩ := u.property
      refine ⟨rvCoprodLeftMap U.obj V.obj r,?_,?_⟩
      · exact (congrArg (rvLeftTag V.obj.arity) hr).trans (congrArg Prod.snd hu)
      · funext i; exact i.elim0
    · obtain ⟨r,hr,_⟩ := v.property
      refine ⟨rvCoprodRightMap U.obj V.obj r,?_,?_⟩
      · exact (congrArg (rvRightTag U.obj.arity) hr).trans (congrArg Prod.snd hv)
      · funext i; exact i.elim0

def ordinaryZeroLiftCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : RVFiniteObject (M := M) (C.base : Set M) 0) :
    vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1)
      (rvLiftFiniteObject (rawRVSpace (M := M) 1) U) (rvLiftFiniteObject (rawRVSpace (M := M) 1) V) ≅
        rvLiftFiniteObject (rawRVSpace (M := M) 1) (rvFiniteCoprodObject U V) := by
  let A := (vfAllCoprodObject (rvLiftObject (rawRVSpace (M := M) 1) U.obj).obj
    (rvLiftObject (rawRVSpace (M := M) 1) V.obj).obj).set
  let B := rvLift (rvCoprodObject U.obj V.obj)
  let f : Map A B := Map.inclusion (fun p hp => (ordinary_zero_lift_coprod_carrier U V p).mpr hp)
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      exact Subtype.ext (congrArg (fun z : B => z.val) h)
    · intro p
      exact ⟨⟨p.val,(ordinary_zero_lift_coprod_carrier U V p.val).mp p.property⟩,rfl⟩
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact DefinableSetCat.isoOfBijective f hf

end IntegrationInACVF.Section7
