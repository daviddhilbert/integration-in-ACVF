import Integration7.AppendedPositiveCoefficientLiftCarriers
import Section4.RVProductSymmetry

/-! The Cartesian coefficient-lift product maps bijectively to the
family-product realization by swapping only its two RV label blocks.
Every VF coordinate is fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

def appendedCoefficientVFProduct (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree n ((p+1)+k)) :=
  ((rvVolumeLift U).prod F.appendedFullLift).reindexDegree (appended_positive_coefficient_degree_eq n p k)

def appendedCoefficientLiftProductMap (F : DefinableVFVolumeFamily C n a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (appendedCoefficientVFProduct F U).domain (F.mulConstant U).appendedFullLift.domain := by
  let P := appendedCoefficientVFProduct F U
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  let f : Map P.domain (DefSet.univ
      (rawMixedSpace (M := M) (appendVolumeDegree n ((p+1)+k)+1) (a+U.underlying.obj.arity)) (C.base : Set M)) :=
    (Map.prodUnivMap (Map.id (DefSet.univ (rawVFSpace (appendVolumeDegree n ((p+1)+k)+1)) (C.base : Set M)))
      (rvReindexMap (C.base : Set M) e)).comp (Map.id P.domain).toUniv
  exact f.corestrict (fun q => by
    let s := q.val.2 ∘ Fin.castAdd a
    let r := q.val.2 ∘ Fin.natAdd U.underlying.obj.arity
    have hRV : Fin.append s r=q.val.2 := Fin.append_castAdd_natAdd
    have hP : (q.val.1,Fin.append s r) ∈ P.domain.carrier := by rw [hRV]; exact q.property
    have hH := (appended_positive_coefficient_lift_carrier F U q.val.1 r s).mpr hP
    have hSwap := rvAppend_flip r s
    change Fin.append s r ∘ e=Fin.append r s at hSwap
    rw [hRV] at hSwap
    change (q.val.1,q.val.2 ∘ e) ∈ (F.mulConstant U).appendedFullLift.domain.carrier
    rw [hSwap]
    exact hH)

theorem appended_coefficient_lift_product_map_value
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (appendedCoefficientVFProduct F U).domain) :
    (appendedCoefficientLiftProductMap F U q).val =
      (q.val.1,q.val.2 ∘ (finAddFlip : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a))) := rfl

theorem appended_coefficient_lift_product_map_bijective
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Function.Bijective (appendedCoefficientLiftProductMap F U) := by
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  constructor
  · intro q r he
    have h := congrArg Subtype.val he
    change (q.val.1,q.val.2 ∘ e)=(r.val.1,r.val.2 ∘ e) at h
    have hx := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    apply Subtype.ext
    refine Prod.ext hx ?_
    funext i
    have hi := congrFun hr (e.symm i)
    simpa only [Function.comp_apply,e.apply_symm_apply] using hi
  · intro q
    let r := q.val.2 ∘ Fin.castAdd U.underlying.obj.arity
    let s := q.val.2 ∘ Fin.natAdd a
    have hRV : Fin.append r s=q.val.2 := Fin.append_castAdd_natAdd
    have hH : (q.val.1,Fin.append r s) ∈ (F.mulConstant U).appendedFullLift.domain.carrier := by
      rw [hRV]
      exact q.property
    have hP := (appended_positive_coefficient_lift_carrier F U q.val.1 r s).mp hH
    refine ⟨⟨(q.val.1,Fin.append s r),hP⟩,?_⟩
    apply Subtype.ext
    change (q.val.1,Fin.append s r ∘ e)=q.val
    have hSwap := rvAppend_flip r s
    change Fin.append s r ∘ e=Fin.append r s at hSwap
    exact Prod.ext rfl (hSwap.trans hRV)

end IntegrationInACVF.Section7
