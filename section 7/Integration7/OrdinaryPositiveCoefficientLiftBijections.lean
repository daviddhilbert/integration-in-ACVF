module

public import Integration7.OrdinaryPositiveCoefficientLiftMaps
public import Integration7.VFVolumeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coefficient-first ordinary-family product chart preserves
the actual positive coefficient density and every VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a p : ℕ}

theorem ordinary_positive_coefficient_lift_map_density
    (F : OrdinaryVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : (ordinaryPositiveCoefficientVFProduct F U).domain) :
    (ordinaryPositiveCoefficientVFProduct F U).form.value q =
      (F.mulConstant U).appendedFullLift.form.value (ordinaryPositiveCoefficientLiftMap F U q) := by
  let P := (rvVolumeLift U).prod F.fullVFObject
  let h := ordinary_positive_coefficient_lift_degree n p
  let q0 : P.domain := ⟨(q.val.1 ∘ (finCongr (congrArg Nat.succ h)).symm,q.val.2),
    (mem_vf_volume_reindex_degree P h q.val.1 q.val.2).mp q.property⟩
  let z := mixedUnpack (rvVolumeLift U).domain F.fullVFObject.domain q0
  let u := Map.prodFst (rvVolumeLift U).domain F.fullVFObject.domain z
  let uBase := liftLabelMap U.underlying.obj u
  let w := (F.mulConstant U).appendedLiftBaseProjection (ordinaryPositiveCoefficientLiftMap F U q)
  let e : Fin (a+U.underlying.obj.arity) ≃ Fin (U.underlying.obj.arity+a) := finAddFlip
  have hz := mixed_product_unpack_value (rvVolumeLift U).domain F.fullVFObject.domain q0
  have hu := congrArg (fun z => z.1.2) hz
  change u.val.2=q.val.2 ∘ Fin.castAdd a at hu
  have hw := congrArg Prod.snd ((F.mulConstant U).appendedLiftBaseProjection_value
    (ordinaryPositiveCoefficientLiftMap F U q))
  change w.val.2=q.val.2 ∘ e at hw
  have hProjection : ordinaryFamilyPositiveCoefficientProjection F U w=uBase := by
    apply Subtype.ext
    have hp := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain w)
    change (ordinaryFamilyPositiveCoefficientProjection F U w).val=w.val.2 ∘ Fin.natAdd a at hp
    refine hp.trans ((congrArg (fun r => r ∘ Fin.natAdd a) hw).trans ?_)
    change (q.val.2 ∘ e) ∘ Fin.natAdd a=u.val.2
    refine (show (q.val.2 ∘ e) ∘ Fin.natAdd a=q.val.2 ∘ Fin.castAdd a from ?_).trans hu.symm
    funext i
    exact congrArg q.val.2 (finAddFlip_apply_natAdd i a)
  have hSource : (ordinaryPositiveCoefficientVFProduct F U).form.value q=U.form.value uBase := by
    have hCast := vf_volume_reindex_degree_density P h q
    change (ordinaryPositiveCoefficientVFProduct F U).form.value q=P.form.value q0 at hCast
    refine hCast.trans ?_
    change U.form.value uBase * 1=U.form.value uBase
    exact mul_one _
  have hTarget : (F.mulConstant U).appendedFullLift.form.value (ordinaryPositiveCoefficientLiftMap F U q)=
      U.form.value uBase := by
    rw [DefinableVFVolumeFamily.appendedFullLift_density]
    change U.form.value (ordinaryFamilyPositiveCoefficientProjection F U w)=_
    rw [hProjection]
  exact hSource.trans hTarget.symm

def ordinaryPositiveCoefficientLiftBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    VFVolumeBijection (ordinaryPositiveCoefficientVFProduct F U) (F.mulConstant U).appendedFullLift :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (ordinaryPositiveCoefficientLiftMap F U)
    (ordinary_positive_coefficient_lift_map_bijective F U) (fun _ => rfl)
    (ordinary_positive_coefficient_lift_map_density F U)

end IntegrationInACVF.Section7
