module

public import Integration7.VFVolumeLifts
public import Section4.MixedProducts
public import Section4.RVProductAssociativity

@[expose] public section

/-! The full ordinary lift of an RV Cartesian product is exactly the
Cartesian product of the two lifts, including coordinate-zero labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

theorem ordinary_lift_product_domain
    (U : RVObject (M := M) S n) (V : RVObject (M := M) S m)
    (p : (Fin (n+m) → VFType (M := M)) ×
      (Fin (U.arity+V.arity) → CanonicalRV.RVSort M)) :
    p ∈ (rvLift (rvProductObject U V)).carrier ↔
      p ∈ (mixedProductDomain (rvLift U) (rvLift V)).carrier := by
  constructor
  · rintro ⟨w,hw,hval⟩
    obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.domain V.domain w
    rw [rvProductObject_value_pair] at hval
    change rvAppend u.val v.val = p.2 at hw
    apply (mem_mixedProductDomain (rvLift U) (rvLift V) p).mpr
    constructor
    · refine ⟨u,?_,?_⟩
      · simpa only [rvAppend,Function.comp_def,Fin.append_left] using
          congrArg (fun r => r ∘ Fin.castAdd V.arity) hw
      · funext i
        change U.value u i = CanonicalRV.encodedRv (p.1 (Fin.castAdd m i))
        simpa only [rvAppend,Fin.append_left,tupleRV] using congrFun hval (Fin.castAdd m i)
    · refine ⟨v,?_,?_⟩
      · simpa only [rvAppend,Function.comp_def,Fin.append_right] using
          congrArg (fun r => r ∘ Fin.natAdd U.arity) hw
      · funext i
        change V.value v i = CanonicalRV.encodedRv (p.1 (Fin.natAdd n i))
        simpa only [rvAppend,Fin.append_right,tupleRV] using congrFun hval (Fin.natAdd n i)
  · intro hp
    obtain ⟨⟨u,hu,hU⟩,⟨v,hv,hV⟩⟩ :=
      (mem_mixedProductDomain (rvLift U) (rvLift V) p).mp hp
    refine ⟨rvPackPair U.domain V.domain u v,?_,?_⟩
    · change rvAppend u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    · rw [rvProductObject_value_pair,hU,hV]
      change Fin.append ((tupleRV p.1) ∘ Fin.castAdd m)
        ((tupleRV p.1) ∘ Fin.natAdd n) = tupleRV p.1
      exact Fin.append_castAdd_natAdd

end IntegrationInACVF.Section7
