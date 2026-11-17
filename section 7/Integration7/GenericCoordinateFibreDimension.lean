module

public import Integration7.HeadFibreRawVolumePresentation
public import Integration7.NativeVolumeDomains
public import Section8.GenericOutputBall
public import Section9.MixedDifferentiationAE

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A VF-small set has a VF-small unary coordinate fibre over every
independent complementary VF tuple. The field argument uses actual
generated subfields, not a dimension-fibration assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

theorem independent_cons_over_tuple_field {K : Type} [Field K] {n : ℕ}
    (E : Subfield K) (x : Fin n → K) (y : Fin 1 → K)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent (tupleField E x) y) :
    AlgebraicIndependent E (Fin.cons (y 0) x) := by
  rw [tupleField_eq_adjoin E x] at hy
  have hsum := hx.sumElim_of_tower (S := IntermediateField.adjoin E (Set.range x))
    (by rintro _ ⟨i,rfl⟩; exact ⟨⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩,rfl⟩) hy
  let e : Fin (n+1) → Fin 1 ⊕ Fin n := Fin.cases (Sum.inl 0) Sum.inr
  have he : Function.Injective e := by
    intro i j h
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [e]
  convert hsum.comp e he using 1
  funext i
  cases i using Fin.cases <;> rfl

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

set_option maxHeartbeats 1600000 in
theorem generic_head_coordinate_fibre_small {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (D : DefSet (rawMixedSpace (M := M) (n+1) a) S)
    (hD : vfDim (rawRVSpace (M := M) 1) D < n+1)
    (x : Fin n → VFType (M := M)) (hx : AlgebraicIndependent (vfParameterField S) x) :
    vfDim (rawRVSpace (M := M) 1)
      (rawSpecialSet hc (coordinateFibre (nativeMixedVolumeDomain hc D) 0 (headFrozenTuple x))) < 1 := by
  let A := rawSpecialSet hc (coordinateFibre (nativeMixedVolumeDomain hc D) 0 (headFrozenTuple x))
  have hsmallA : Cardinal.mk (coordinateFibreBase S 0 (headFrozenTuple x)) < κ := by
    rw [head_coordinate_fibre_base]
    exact small_union_range hκ S hsmall (fun j => (x j).val)
  apply mixed_vfDim_lt_of_no_independent hc hs hsmallA (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Nat.one_pos A
  intro p hp
  have hp' : AlgebraicIndependent (tupleField (vfParameterField S) x) p.val.1 := by
    have hField : vfParameterField (coordinateFibreBase S 0 (headFrozenTuple x)) =
        tupleField (vfParameterField S) x := by
      rw [head_coordinate_fibre_base]
      exact vfParameterField_union_tuple S x
    exact Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) =>
      AlgebraicIndependent E p.val.1) hField) hp
  have hcons := independent_cons_over_tuple_field (vfParameterField S) x p.val.1 hx hp'
  let q : D := ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩
  have hq : q.val.1 = Fin.cons (p.val.1 0) x := congrArg Prod.fst (coordinateInsert_head x p.val)
  have hqInd : AlgebraicIndependent (vfParameterField S) q.val.1 := hq.symm ▸ hcons
  have hRank : vfTupleTrdeg S q.val.1 = (n+1 : ℕ) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) q.val.1).mpr hqInd
  have hle := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) D q
  rw [hRank] at hle
  have hleNat : n+1 ≤ vfDim (rawRVSpace (M := M) 1) D := by exact_mod_cast hle
  exact (Nat.not_le_of_lt hD) hleNat

end IntegrationInACVF.Section7
