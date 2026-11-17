module

public import Integration7.FixedVFVolumeTagBijections
public import Integration7.VFVolumeUnionBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Full volume bijections are compatible with fixed-degree disjoint
unions. The two summand maps are conjugated by their actual RV tags. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VFVolumeBijection.coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U U') (g : VFVolumeBijection V V') :
    VFVolumeBijection (U.coprod V) (U'.coprod V') := by
  let L := ((vfVolumeLeftTagBijection hc C U V.arity).symm hc C).trans hc C
    (f.trans hc C (vfVolumeLeftTagBijection hc C U' V'.arity))
  let R := ((vfVolumeRightTagBijection hc C V U.arity).symm hc C).trans hc C
    (g.trans hc C (vfVolumeRightTagBijection hc C V' U'.arity))
  exact ⟨unionMixedMap L.map R.map,
    unionMixedMap_bijective (fixed_vf_tagged_images_disjoint U.domain V.domain)
      (fixed_vf_tagged_images_disjoint U'.domain V'.domain)
      L.map R.map L.bijective R.bijective,
    preservesVFVolume_unionMixedMap hc C (Nat.zero_lt_succ k)
      (fixed_vf_tagged_images_disjoint U.domain V.domain)
      (fixed_vf_tagged_images_disjoint U'.domain V'.domain)
      L.map R.map L.bijective.1 R.bijective.1
      _ _ _ _ L.preserves R.preserves⟩

end IntegrationInACVF.Section7
