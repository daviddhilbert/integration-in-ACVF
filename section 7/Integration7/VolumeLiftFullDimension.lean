module

public import Integration7.VFVolumeLifts
public import Section4.FullDimension
public import Section4.RVWeightDimension

@[expose] public section

/-! A nonempty essential RV object lifts to full VF dimension. Thus an
RV volume object with a VF-small lift has no essential labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem volume_lift_full_dimension_of_essential_point
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (u : U.essential.obj.domain) :
    vfDim (rawRVSpace (M := M) 1) (rvVolumeLift U).domain = k+1 := by
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  let w : U.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩
  let t := U.underlying.obj.value w
  obtain ⟨c,hcRV⟩ := tupleRV_surjective t
  have hc0 (i : Fin (k+1)) : c i ≠ 0 := by
    intro hz
    exact U.essential_nonzero u i
      ((congrArg Subtype.val (congrFun hcRV i)).symm.trans ((CanonicalRV.encodedRv_zero_iff _).mpr hz))
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) (Values.presentationType (M := M))) (k+1) :=
    ⟨c,c,hc0⟩
  have hRV (x : Fin (k+1) → VFType (M := M)) (hx : x ∈ D.carrier) : tupleRV x = t := by
    apply Eq.trans (b := tupleRV c) ?_ hcRV
    funext i
    apply Subtype.ext
    apply (CanonicalRV.encoded_eq_iff_close (x i).property (c i).property
      (fun h => hc0 i (Subtype.ext h))).mpr
    change ¬ VFValued.predV (c i) (x i - c i)
    rw [Values.presentation_compatible,not_le]
    exact hx i
  exact vfDim_eq_arity_of_contains_polydisc hc C.saturated C.small
    (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Values.presentation_compatible
    (rvVolumeLift U).domain u.val D (fun x hx => ⟨w,rfl,(hRV x hx).symm⟩)

theorem essential_empty_of_volume_lift_small_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rvVolumeLift U).domain < k+1) :
    U.essential.obj.domain.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hdim := volume_lift_full_dimension_of_essential_point hc C U ⟨r,hr⟩
  rw [hdim] at hsmall
  exact (Nat.lt_irrefl _) hsmall

end IntegrationInACVF.Section7
