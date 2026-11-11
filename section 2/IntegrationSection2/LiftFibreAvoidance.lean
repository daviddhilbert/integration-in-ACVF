import Section4.RVWeightDimension

/-! Every nondegenerate actual lifted RV fibre escapes any actual
VF-small set. The proof constructs a full polydisc in the fixed label
fibre and uses the checked concrete VF dimension theorem. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.LiftFibreAvoidance

variable {M Γ : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
  [LinearOrderedCommGroupWithZero Γ] [Valued (VFType (M := M)) Γ] {S : Set M} {k : ℕ}

theorem exists_outside (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : RVObject (M := M) S k) (u : U.domain) (hUnit : ∀ i, (U.value u i).val ≠ iRVZero)
    (Z : DefSet (rawMixedSpace (M := M) k U.arity) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < k) :
    ∃ p : rvLift U, p.val.2 = u.val ∧ p.val ∉ Z.carrier := by
  classical
  obtain ⟨a,ha⟩ := tupleRV_surjective (U.value u)
  have ha0 (i : Fin k) : a i ≠ 0 := by
    intro h0
    apply hUnit i
    have he := congrArg Subtype.val (congrFun ha i)
    change (CanonicalRV.encodedRv (a i)).val = (U.value u i).val at he
    exact he.symm.trans ((CanonicalRV.encodedRv_zero_iff (a i)).mpr h0)
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) Γ) k := ⟨a,a,ha0⟩
  have hRV (x : Fin k → VFType (M := M)) (hx : x ∈ D.carrier) : tupleRV x = U.value u := by
    have he : tupleRV x = tupleRV a := by
      funext i
      apply Subtype.ext
      apply (CanonicalRV.encoded_eq_iff_close (x i).property (a i).property
        (fun h => ha0 i (Subtype.ext h))).mpr
      change ¬ VFValued.predV (a i) (x i-a i)
      rw [hv,not_le]
      exact hx i
    exact he.trans ha
  by_contra hNo
  have hBox (x : Fin k → VFType (M := M)) (hx : x ∈ D.carrier) : (x,u.val) ∈ Z.carrier := by
    let p : rvLift U := ⟨(x,u.val),⟨u,rfl,(hRV x hx).symm⟩⟩
    by_contra hp
    exact hNo ⟨p,rfl,hp⟩
  have hFull := vfDim_eq_arity_of_contains_polydisc hc hs hsmall (rawRVSpace (M := M) 1)
    (rawRVSpace_rvCoded 1) hv Z u.val D hBox
  rw [hFull] at hZ
  exact (lt_irrefl k) hZ

end IntegrationInACVF.Section2.LiftFibreAvoidance
