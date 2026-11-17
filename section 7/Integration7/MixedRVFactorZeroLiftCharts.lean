module

public import Integration7.MixedRVFactorDomains
public import Integration7.OrdinaryZeroLiftIsomorphisms
public import Section4.MixedProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A pure RV factor and its ordinary zero-dimensional VF lift have
the same mixed product carrier. The coordinate formula for mixed unpacking
keeps the original VF tuple and the first RV block literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem mem_ordinary_zero_volume_lift (Z : RVFiniteObject (M := M) S 0)
    (x : Fin 0 → VFType (M := M)) (r : Fin Z.obj.arity → CanonicalRV.RVSort M) :
    (x,r) ∈ (rvLift Z.obj).carrier ↔ r ∈ Z.obj.domain.carrier := by
  constructor
  · rintro ⟨u,hu,hv⟩
    change u.val=r at hu
    exact Eq.mp (congrArg (fun s => s ∈ Z.obj.domain.carrier) hu) u.property
  · intro hr
    exact ⟨⟨r,hr⟩,rfl,funext (fun i => i.elim0)⟩

theorem mixed_rv_factor_zero_lift_carrier
    (A : DefSet (rawMixedSpace (M := M) n a) S) (Z : RVFiniteObject (M := M) S 0) :
    (mixedRVFactorDomain A Z.obj.domain).carrier = (mixedProductDomain A (rvLift Z.obj)).carrier := by
  ext w
  change (w.1,w.2) ∈ (mixedRVFactorDomain A Z.obj.domain).carrier ↔
    (w.1,w.2) ∈ (mixedProductDomain A (rvLift Z.obj)).carrier
  rw [mem_mixed_rv_factor_domain,mem_mixedProductDomain,mem_ordinary_zero_volume_lift]
  have hx : w.1 ∘ Fin.castAdd 0 = w.1 := by funext i; rfl
  rw [hx]

theorem mixed_zero_product_first_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (Z : RVFiniteObject (M := M) S 0)
    (p : mixedProductDomain A (rvLift Z.obj)) :
    ((mixedUnpack A (rvLift Z.obj) p).val.1) = (p.val.1,p.val.2 ∘ Fin.castAdd Z.obj.arity) := by
  let q := mixedUnpack A (rvLift Z.obj) p
  have h := congrArg Subtype.val (mixedPack_unpack A (rvLift Z.obj) p)
  change (Fin.append (m := n) (n := 0) q.val.1.1 q.val.2.1,
    Fin.append (m := a) (n := Z.obj.arity) q.val.1.2 q.val.2.2) = p.val at h
  have hx := congrArg Prod.fst h
  have hx' : q.val.1.1=p.val.1 := by
    funext i
    have hi := congrFun hx (Fin.castAdd 0 i)
    change Fin.append (m := n) (n := 0) q.val.1.1 q.val.2.1 (Fin.castAdd 0 i) = p.val.1 (Fin.castAdd 0 i) at hi
    rw [Fin.append_left] at hi
    exact hi.trans (congrArg p.val.1 (Fin.ext rfl))
  have hr : q.val.1.2=p.val.2 ∘ Fin.castAdd Z.obj.arity := by
    funext i
    simpa only [Fin.append_left,Function.comp_apply] using congrArg (fun w => w.2 (Fin.castAdd Z.obj.arity i)) h
  exact Prod.ext hx' hr

end IntegrationInACVF.Section7
