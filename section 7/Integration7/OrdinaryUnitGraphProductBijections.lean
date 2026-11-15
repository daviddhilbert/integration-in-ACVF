import Integration7.OrdinaryUnitSelectedVolumeFamilies
import Integration7.OrdinaryVolumeFamilyScalarProducts
import Integration7.VFVolumeBijections
import Section4.UnionMapLaws

/-! Removing an ordinary family's unit-density graph remains an
actual VF-volume bijection after multiplication by any finite RV[0]
factor. The VF tuple and the unit density are retained literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable {C : BaseContext M}

def OrdinaryVFVolumeFamily.unitGraph (F : OrdinaryVFVolumeFamily C (n+1) a) :
    OrdinaryVFVolumeFamily C (n+1) (a+1) where
  domain := F.fullVFObject.densityGraph.domain
  finite_labels := F.fullVFObject.densityGraph.finite_labels

def ordinaryUnitGraphProductVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : OrdinaryVFVolumeFamily C (n+1) a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VFVolumeBijection ((F.unitGraph.prodZero Z).fullVFObject) ((F.prodZero Z).fullVFObject) := by
  let A := F.unitGraph.domain
  let R := Z.obj.domain
  let g := densityGraphProjection F.fullVFObject.form
  have hg : Function.Bijective g := by
    constructor
    · exact Map.inverse_injective _ (appendDensityMap_toImage_bijective F.fullVFObject.form)
    · intro p
      exact ⟨(appendDensityMap F.fullVFObject.form).toImage p,Map.inverse_apply _ _ p⟩
  have hUnpack : Function.Bijective (mixedRVFactorUnpack A R) := by
    constructor
    · exact Map.inverse_injective _ (mixed_rv_factor_pack_to_image_bijective A R)
    · intro p
      exact ⟨(mixedRVFactorPack A R).toImage p,mixed_rv_factor_unpack_pack A R p⟩
  let h := Map.prodMap g (Map.id R)
  let f := (mixedRVFactorPack F.domain R).toImage.comp (h.comp (mixedRVFactorUnpack A R))
  have hf : Function.Bijective f := (mixed_rv_factor_pack_to_image_bijective F.domain R).comp
    ((Map.prodMap_bijective g (Map.id R) hg Function.bijective_id).comp hUnpack)
  apply VFVolumeBijection.of_preserving_vf_and_density hc C f hf
  · intro p
    change (densityGraphProjection F.fullVFObject.form
      (Map.prodFst A R (mixedRVFactorUnpack A R p))).val.1=p.val.1
    rw [densityGraphProjection_value]
    exact congrArg (fun v => v.1.1) (mixed_rv_factor_unpack_value A R p)
  · intro p
    rfl
end IntegrationInACVF.Section7
