module

public import Integration7.AppendedCoefficientLiftProductMaps
public import Integration7.MixedProductCoordinateFormulas

@[expose] public section

/-! The coefficient-first product chart fixes the VF coordinates and
preserves the product of the original coefficient and family densities.
It is therefore a genuine full VF volume bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}

theorem appended_coefficient_lift_product_map_density
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (appendedCoefficientVFProduct F U).domain) :
    (appendedCoefficientVFProduct F U).form.value q =
      (F.mulConstant U).appendedFullLift.form.value (appendedCoefficientLiftProductMap F U q) := by
  let P := (rvVolumeLift U).prod F.appendedFullLift
  let h := appended_positive_coefficient_degree_eq n p k
  let q0 : P.domain := ⟨(q.val.1 ∘ (finCongr (congrArg Nat.succ h)).symm,q.val.2),
    (mem_vf_volume_reindex_degree P h q.val.1 q.val.2).mp q.property⟩
  let z := mixedUnpack (rvVolumeLift U).domain F.appendedFullLift.domain q0
  let u := Map.prodFst (rvVolumeLift U).domain F.appendedFullLift.domain z
  let v := Map.prodSnd (rvVolumeLift U).domain F.appendedFullLift.domain z
  let fBase := F.appendedLiftBaseProjection v
  let uBase := liftLabelMap U.underlying.obj u
  let w := (mixedRVFactorPack F.domain U.underlying.obj.domain).toImage
    ⟨(fBase.val,uBase.val),fBase.property,uBase.property⟩
  have hz := mixed_product_unpack_value (rvVolumeLift U).domain F.appendedFullLift.domain q0
  have hvVF := congrArg (fun z => z.2.1) hz
  have huRV := congrArg (fun z => z.1.2) hz
  have hvRV := congrArg (fun z => z.2.2) hz
  change v.val.1=appendedPositiveCoefficientTail n p k q.val.1 at hvVF
  change u.val.2=q.val.2 ∘ Fin.castAdd a at huRV
  change v.val.2=q.val.2 ∘ Fin.natAdd U.underlying.obj.arity at hvRV
  have hLabels : Fin.append (m := U.underlying.obj.arity) (n := a) u.val.2 v.val.2=q.val.2 :=
    (congrArg₂ (fun r s => Fin.append r s) huRV hvRV).trans Fin.append_castAdd_natAdd
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  have hSwap := rvAppend_flip v.val.2 u.val.2
  change Fin.append (m := U.underlying.obj.arity) (n := a) u.val.2 v.val.2 ∘ e=Fin.append v.val.2 u.val.2 at hSwap
  rw [hLabels] at hSwap
  have hF := F.appendedLiftBaseProjection_value v
  have hFBase := congrArg Prod.fst hF
  have hFLabels := congrArg Prod.snd hF
  have hBase : (F.mulConstant U).appendedLiftBaseProjection (appendedCoefficientLiftProductMap F U q)=w := by
    apply Subtype.ext
    have hH := (F.mulConstant U).appendedLiftBaseProjection_value (appendedCoefficientLiftProductMap F U q)
    change ((F.mulConstant U).appendedLiftBaseProjection (appendedCoefficientLiftProductMap F U q)).val=
      (appendedFamilyBaseCoordinates n ((p+1)+k) q.val.1,q.val.2 ∘ e) at hH
    refine hH.trans ?_
    change (appendedFamilyBaseCoordinates n ((p+1)+k) q.val.1,q.val.2 ∘ e)=
      (fBase.val.1,Fin.append fBase.val.2 uBase.val)
    refine Prod.ext ?_ ?_
    · exact (appended_positive_coefficient_base_coordinates n p k q.val.1).trans
        ((congrArg (appendedFamilyBaseCoordinates n k) hvVF.symm).trans hFBase.symm)
    · exact hSwap.trans (congrArg₂ (fun r s => Fin.append r s) hFLabels.symm rfl)
  have hSource : (appendedCoefficientVFProduct F U).form.value q=U.form.value uBase * F.form.value fBase := by
    have hCast := vf_volume_reindex_degree_density P h q
    change (appendedCoefficientVFProduct F U).form.value q=P.form.value q0 at hCast
    refine hCast.trans ?_
    change U.form.value uBase * F.appendedFullLift.form.value v=U.form.value uBase * F.form.value fBase
    rw [DefinableVFVolumeFamily.appendedFullLift_density]
  have hTarget : (F.mulConstant U).appendedFullLift.form.value (appendedCoefficientLiftProductMap F U q)=
      U.form.value uBase * F.form.value fBase := by
    rw [DefinableVFVolumeFamily.appendedFullLift_density,hBase]
    change (volumeFamilyConstantForm F U).value w=_
    rw [volume_family_constant_density]
    change U.form.value (Map.prodSnd _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain w)) *
      F.form.value (Map.prodFst _ _ (mixedRVFactorUnpack F.domain U.underlying.obj.domain w))=_
    rw [mixed_rv_factor_unpack_pack]
    rfl
  exact hSource.trans hTarget.symm

def appendedCoefficientLiftProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : DefinableVFVolumeFamily C n a k) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    VFVolumeBijection (appendedCoefficientVFProduct F U) (F.mulConstant U).appendedFullLift :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (appendedCoefficientLiftProductMap F U)
    (appended_coefficient_lift_product_map_bijective F U) (fun _ => rfl)
    (appended_coefficient_lift_product_map_density F U)

end IntegrationInACVF.Section7
