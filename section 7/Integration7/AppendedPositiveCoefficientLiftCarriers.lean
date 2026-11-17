module

public import Integration7.AppendedPositiveCoefficientCoordinates
public import Integration7.DefinableAppendedLiftCarriers
public import Integration7.VolumeFamilyPositiveCoefficientProducts
public import Integration7.PositiveVFVolumeProducts
public import Integration7.VFVolumeLifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coefficient-first realization of a positive constant-family
product has exactly the Cartesian coefficient-lift carrier. Only the
old RV label blocks are swapped; the VF blocks keep their stated order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

theorem appended_positive_coefficient_lift_carrier
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (x : Fin (appendVolumeDegree n ((p+1)+k)+1) → VFType (M := M))
    (r : Fin a → CanonicalRV.RVSort M) (s : Fin U.underlying.obj.arity → CanonicalRV.RVSort M) :
    (x,Fin.append r s) ∈ (F.mulConstant U).appendedFullLift.domain.carrier ↔
      (x,Fin.append s r) ∈ (((rvVolumeLift U).prod F.appendedFullLift).reindexDegree
        (appended_positive_coefficient_degree_eq n p k)).domain.carrier := by
  let H := F.mulConstant U
  rw [mem_vf_volume_reindex_degree]
  change (x,Fin.append r s) ∈ H.appendedFullLift.domain.carrier ↔
    (x ∘ (finCongr (congrArg Nat.succ (appended_positive_coefficient_degree_eq n p k))).symm,Fin.append s r) ∈
      (mixedProductDomain (n := p+1) (m := appendVolumeDegree n k+1) (rvLift U.underlying.obj) F.appendedFullLift.domain).carrier
  rw [mem_mixedProductDomain]
  change (x,Fin.append r s) ∈ H.appendedFullLift.domain.carrier ↔
    (appendedPositiveCoefficientHead n p k x,Fin.append s r ∘ Fin.castAdd a) ∈ (rvLift U.underlying.obj).carrier ∧
      (appendedPositiveCoefficientTail n p k x,Fin.append s r ∘ Fin.natAdd U.underlying.obj.arity) ∈ F.appendedFullLift.domain.carrier
  have hs : Fin.append s r ∘ Fin.castAdd a=s := funext (Fin.append_left _ _)
  have hr : Fin.append s r ∘ Fin.natAdd U.underlying.obj.arity=r := funext (Fin.append_right _ _)
  rw [hs,hr,mem_definable_appended_family_lift H x (Fin.append r s),
    mem_definable_appended_family_lift F (appendedPositiveCoefficientTail n p k x) r]
  constructor
  · rintro ⟨q,hq,ht⟩
    let f := volumeFamilyConstantBaseProjection F U q
    let u := volumeFamilyConstantCoefficientProjection F U q
    have hPoints := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q
    rw [hq] at hPoints
    change (f.val,u.val)=((appendedFamilyBaseCoordinates n ((p+1)+k) x,
      Fin.append r s ∘ Fin.castAdd U.underlying.obj.arity),Fin.append r s ∘ Fin.natAdd a) at hPoints
    simp only [Function.comp_def,Fin.append_left,Fin.append_right] at hPoints
    have hf := congrArg Prod.fst hPoints
    have hu := congrArg Prod.snd hPoints
    change tupleRV (appendedFamilyCoefficientCoordinates n ((p+1)+k) x)=
      Fin.append (m := p+1) (n := k+1) (U.underlying.obj.value u) (F.volume f).val at ht
    have hU : tupleRV (appendedPositiveCoefficientHead n p k x)=U.underlying.obj.value u := by
      rw [← appended_positive_coefficient_head_coordinates]
      funext i
      simpa only [tupleRV,Function.comp_apply,Fin.append_left] using congrFun ht (Fin.castAdd (k+1) i)
    have hF : tupleRV (appendedFamilyCoefficientCoordinates n k (appendedPositiveCoefficientTail n p k x))=(F.volume f).val := by
      rw [← appended_positive_coefficient_tail_coordinates]
      funext i
      simpa only [tupleRV,Function.comp_apply,Fin.append_right] using congrFun ht (Fin.natAdd (p+1) i)
    refine ⟨⟨u,hu,hU.symm⟩,f,?_,hF⟩
    exact hf.trans (Prod.ext (appended_positive_coefficient_base_coordinates n p k x) rfl)
  · rintro ⟨⟨u,hu,hU⟩,f,hf,hF⟩
    let q := (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
      ⟨(f.val,u.val),f.property,u.property⟩
    have hx := congrArg Prod.fst hf
    have hrF := congrArg Prod.snd hf
    have hq : q.val=(appendedFamilyBaseCoordinates n ((p+1)+k) x,Fin.append r s) := by
      change (f.val.1,Fin.append f.val.2 u.val)=_
      exact Prod.ext (hx.trans (appended_positive_coefficient_base_coordinates n p k x).symm)
        (congrArg₂ (fun r s => Fin.append r s) hrF hu)
    refine ⟨q,hq,?_⟩
    have hVolume : (H.volume q).val=Fin.append (U.underlying.obj.value u) (F.volume f).val := by
      change (volumeFamilyConstantVolumeMap F U q).val=_
      rw [volume_family_constant_volume]
      change Fin.append (U.underlying.obj.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain q)))
        (F.volume (Map.prodFst _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain q))).val=_
      rw [mixed_rv_factor_unpack_pack]
      rfl
    rw [hVolume]
    funext i
    refine Fin.addCases (m := p+1) (n := k+1) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      have hi := congrFun (appended_positive_coefficient_head_coordinates n p k x) j
      exact (congrArg CanonicalRV.encodedRv hi).trans (congrFun hU j).symm
    · rw [Fin.append_right]
      have hi := congrFun (appended_positive_coefficient_tail_coordinates n p k x) j
      exact (congrArg CanonicalRV.encodedRv hi).trans (congrFun hF j)

end IntegrationInACVF.Section7
