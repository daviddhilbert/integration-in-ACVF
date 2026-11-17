module

public import Integration7.HKZeroFamilyPositiveCoefficients
public import Integration7.HKZeroPositiveCoefficientLiftMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coefficient-first realization of a positive coefficient times
weighted-zero values preserves the product of both actual forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

theorem zero_positive_coefficient_lift_map_density
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (zeroPositiveCoefficientVFProduct F U).domain) :
    (zeroPositiveCoefficientVFProduct F U).form.value q =
      (F.mulConstant U).appendedFullLift.form.value (zeroPositiveCoefficientLiftMap F U q) := by
  let P := (rvVolumeLift U).prod F.fullVFObject
  let h := zero_positive_coefficient_lift_degree n p
  let q0 : P.domain := ⟨(q.val.1 ∘ (finCongr (congrArg Nat.succ h)).symm,q.val.2),
    (mem_vf_volume_reindex_degree P h q.val.1 q.val.2).mp q.property⟩
  let z := mixedUnpack (rvVolumeLift U).domain F.fullVFObject.domain q0
  let u := Map.prodFst (rvVolumeLift U).domain F.fullVFObject.domain z
  let v := Map.prodSnd (rvVolumeLift U).domain F.fullVFObject.domain z
  let uBase := liftLabelMap U.underlying.obj u
  let w := (F.mulConstant U).appendedLiftBaseProjection (zeroPositiveCoefficientLiftMap F U q)
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  have hz := mixed_product_unpack_value (rvVolumeLift U).domain F.fullVFObject.domain q0
  have hu := congrArg (fun z => z.1.2) hz
  change u.val.2=q.val.2 ∘ Fin.castAdd a at hu
  have hvVF := congrArg (fun z => z.2.1) hz
  have hvRV := congrArg (fun z => z.2.2) hz
  change v.val.2=q.val.2 ∘ Fin.natAdd U.underlying.obj.arity at hvRV
  have hw := (F.mulConstant U).appendedLiftBaseProjection_value (zeroPositiveCoefficientLiftMap F U q)
  change w.val=(appendedFamilyBaseCoordinates (n+1) p q.val.1,q.val.2 ∘ e) at hw
  let unpack := mixedRVFactorUnpack F.domain U.underlying.obj.domain w
  have hUnpack := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain w
  have hProjectionU : Map.prodSnd _ _ unpack=uBase := by
    apply Subtype.ext
    have hp := congrArg Prod.snd hUnpack
    change (Map.prodSnd _ _ unpack).val=w.val.2 ∘ Fin.natAdd a at hp
    refine hp.trans ((congrArg (fun r => r.2 ∘ Fin.natAdd a) hw).trans ?_)
    refine (show (q.val.2 ∘ e) ∘ Fin.natAdd a=q.val.2 ∘ Fin.castAdd a from ?_).trans hu.symm
    funext i
    exact congrArg q.val.2 (finAddFlip_apply_natAdd i a)
  have hProjectionF : Map.prodFst _ _ unpack=v := by
    apply Subtype.ext
    have hp := congrArg Prod.fst hUnpack
    refine hp.trans ?_
    change (w.val.1,w.val.2 ∘ Fin.castAdd U.underlying.obj.arity)=v.val
    refine Prod.ext ?_ ?_
    · refine (congrArg Prod.fst hw).trans ?_
      exact hvVF.symm
    · refine (congrArg (fun r => r.2 ∘ Fin.castAdd U.underlying.obj.arity) hw).trans ?_
      refine (show (q.val.2 ∘ e) ∘ Fin.castAdd U.underlying.obj.arity=
        q.val.2 ∘ Fin.natAdd U.underlying.obj.arity from ?_).trans hvRV.symm
      funext i
      exact congrArg q.val.2 (finAddFlip_apply_castAdd i U.underlying.obj.arity)
  have hSource : (zeroPositiveCoefficientVFProduct F U).form.value q=
      U.form.value uBase * F.form.value v := by
    exact vf_volume_reindex_degree_density P h q
  have hTarget : (F.mulConstant U).appendedFullLift.form.value (zeroPositiveCoefficientLiftMap F U q)=
      F.form.value v * U.form.value uBase := by
    rw [DefinableVFVolumeFamily.appendedFullLift_density]
    change F.form.value (Map.prodFst _ _ unpack) * U.form.value (Map.prodSnd _ _ unpack)=_
    rw [hProjectionF,hProjectionU]
  exact hSource.trans ((mul_comm _ _).trans hTarget.symm)

def zeroPositiveCoefficientLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    VFVolumeBijection (zeroPositiveCoefficientVFProduct F U) (F.mulConstant U).appendedFullLift :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (zeroPositiveCoefficientLiftMap F U)
    (zero_positive_coefficient_lift_map_bijective F U) (fun _ => rfl)
    (zero_positive_coefficient_lift_map_density F U)

end IntegrationInACVF.Section7.HK
