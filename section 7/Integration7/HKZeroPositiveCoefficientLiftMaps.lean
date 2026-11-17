module

public import Integration7.HKZeroPositiveCoefficientLiftCarriers
public import Section4.RVProductSymmetry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coefficient-first Cartesian realization maps to the ordinary
family product by swapping only the RV domain-label blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

def zeroPositiveCoefficientLiftMap (F : ZeroVFVolumeFamily C (n+1) a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Map (zeroPositiveCoefficientVFProduct F U).domain (F.mulConstant U).appendedFullLift.domain := by
  let P := zeroPositiveCoefficientVFProduct F U
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  let f : Map P.domain (DefSet.univ
      (rawMixedSpace (M := M) (appendVolumeDegree (n+1) p+1) (a+U.underlying.obj.arity)) (C.base : Set M)) :=
    (Map.prodUnivMap (Map.id (DefSet.univ (rawVFSpace (appendVolumeDegree (n+1) p+1)) (C.base : Set M)))
      (rvReindexMap (C.base : Set M) e)).comp (Map.id P.domain).toUniv
  exact f.corestrict (fun q => by
    let s := q.val.2 ∘ Fin.castAdd a
    let r := q.val.2 ∘ Fin.natAdd U.underlying.obj.arity
    have hRV : Fin.append s r=q.val.2 := Fin.append_castAdd_natAdd
    have hP : (q.val.1,Fin.append s r) ∈ P.domain.carrier := by rw [hRV]; exact q.property
    have hH := (zero_positive_coefficient_lift_carrier F U q.val.1 r s).mpr hP
    have hSwap := rvAppend_flip r s
    change Fin.append s r ∘ e=Fin.append r s at hSwap
    rw [hRV] at hSwap
    change (q.val.1,q.val.2 ∘ e) ∈ (F.mulConstant U).appendedFullLift.domain.carrier
    rw [hSwap]
    exact hH)

theorem zero_positive_coefficient_lift_map_value
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (zeroPositiveCoefficientVFProduct F U).domain) :
    (zeroPositiveCoefficientLiftMap F U q).val =
      (q.val.1,q.val.2 ∘ (finAddFlip : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a))) := rfl

theorem zero_positive_coefficient_lift_map_bijective
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    Function.Bijective (zeroPositiveCoefficientLiftMap F U) := by
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
    have hP := (zero_positive_coefficient_lift_carrier F U q.val.1 r s).mp hH
    refine ⟨⟨(q.val.1,Fin.append s r),hP⟩,?_⟩
    apply Subtype.ext
    change (q.val.1,Fin.append s r ∘ e)=q.val
    have hSwap := rvAppend_flip r s
    change Fin.append s r ∘ e=Fin.append r s at hSwap
    exact Prod.ext rfl (hSwap.trans hRV)

end IntegrationInACVF.Section7.HK
