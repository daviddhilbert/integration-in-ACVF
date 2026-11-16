import Integration7.HKZeroFamilyScalarProducts
import Integration7.HKWeightedVFZeroClassProducts
import Integration7.MixedRVFactorZeroLiftCharts

/-! The weighted scalar family realizes the actual Cartesian product
with the coefficient's full weighted zero lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def zeroVolumeScalarRealizationBijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VFVolumeBijection (F.prodZero Z).fullVFObject (positiveVFZeroProduct F.fullVFObject Z) := by
  have he : (F.prodZero Z).fullVFObject.domain.carrier =
      (positiveVFZeroProduct F.fullVFObject Z).domain.carrier :=
    mixed_rv_factor_zero_lift_carrier F.domain Z.underlying
  let f : Map (F.prodZero Z).fullVFObject.domain (positiveVFZeroProduct F.fullVFObject Z).domain :=
    Map.inclusion he.le
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      exact Subtype.ext (congrArg (fun w : (positiveVFZeroProduct F.fullVFObject Z).domain => w.val) h)
    · intro p
      exact ⟨⟨p.val,he.ge p.property⟩,rfl⟩
  refine VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) ?_
  intro p
  obtain ⟨uv,rfl⟩ := (mixed_rv_factor_pack_to_image_bijective F.domain Z.underlying.obj.domain).2 p
  let u := Map.prodFst F.domain Z.underlying.obj.domain uv
  let v := Map.prodSnd F.domain Z.underlying.obj.domain uv
  let z : rvLift Z.underlying.obj := ⟨(Fin.elim0,v.val),⟨v,rfl,funext (fun i => i.elim0)⟩⟩
  have hp : f ((mixedRVFactorPack F.domain Z.underlying.obj.domain).toImage uv) =
      (mixedPack F.domain (rvLift Z.underlying.obj)).toImage ⟨(u.val,z.val),u.property,z.property⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact (Fin.append_left u.val.1 z.val.1 i).symm
    · rfl
  change (F.form.prod Z.form).value (mixedRVFactorUnpack F.domain Z.underlying.obj.domain
    ((mixedRVFactorPack F.domain Z.underlying.obj.domain).toImage uv)) = _
  rw [mixed_rv_factor_unpack_pack,hp]
  exact (positiveVFZeroProduct_density_pair F.fullVFObject Z u z).symm

theorem zero_volume_family_scalar_full_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    positiveVFVolumeIsoClass hc C (F.prodZero Z).fullVFObject =
      positiveVFZeroCoefficientProduct hc C (positiveVFVolumeIsoClass hc C F.fullVFObject)
        (rvVolumeBlowupClass hc C (n := 0) Z) :=
  (positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (zeroVolumeScalarRealizationBijection hc F Z)⟩

end IntegrationInACVF.Section7.HK
