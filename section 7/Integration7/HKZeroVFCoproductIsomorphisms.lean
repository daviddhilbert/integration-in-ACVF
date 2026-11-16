module

public import Integration7.HKZeroVFCoproducts

@[expose] public section

/-! The actual tagged weighted zero VF coproduct respects exact-form
isomorphisms, including different ambient mixed presentations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def vfCoprodAmbientIso {A A' B B' : VFAllObject (M := M) S}
    (f : A ≅ A') (g : B ≅ B') : vfAllCoprodObject A B ≅ vfAllCoprodObject A' B' where
  hom := vfAllCoprodDesc (f.hom ≫ vfAllCoprodInl A' B') (g.hom ≫ vfAllCoprodInr A' B')
  inv := vfAllCoprodDesc (f.inv ≫ vfAllCoprodInl A B) (g.inv ≫ vfAllCoprodInr A B)
  hom_inv_id := by
    apply vfAllCoprod_hom_ext
    · rw [← Category.assoc,vfAllCoprodInl_desc,Category.assoc,vfAllCoprodInl_desc,
        ← Category.assoc,f.hom_inv_id,Category.id_comp,Category.comp_id]
    · rw [← Category.assoc,vfAllCoprodInr_desc,Category.assoc,vfAllCoprodInr_desc,
        ← Category.assoc,g.hom_inv_id,Category.id_comp,Category.comp_id]
  inv_hom_id := by
    apply vfAllCoprod_hom_ext
    · rw [← Category.assoc,vfAllCoprodInl_desc,Category.assoc,vfAllCoprodInl_desc,
        ← Category.assoc,f.inv_hom_id,Category.id_comp,Category.comp_id]
    · rw [← Category.assoc,vfAllCoprodInr_desc,Category.assoc,vfAllCoprodInr_desc,
        ← Category.assoc,g.inv_hom_id,Category.id_comp,Category.comp_id]

def zeroVFCoprodIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A A' B B' : ZeroVFVolumeObject (M := M) (C.base : Set M)}
    (f : ZeroVFVolumeIso A A') (g : ZeroVFVolumeIso B B') :
    ZeroVFVolumeIso (zeroVFCoprod hc C A B) (zeroVFCoprod hc C A' B') := by
  let F := ordinaryFiniteAmbientIso f.iso
  let G := ordinaryFiniteAmbientIso g.iso
  let E := vfCoprodAmbientIso F G
  let e : (zeroVFCoprod hc C A B).underlying ≅ (zeroVFCoprod hc C A' B').underlying := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact E
  refine ⟨e,?_⟩
  intro w
  rcases zero_vf_coprod_cases hc C A B w with ⟨u,hu⟩ | ⟨v,hv⟩
  · have hm := congrArg (fun k : A.underlying.obj.obj ⟶ vfAllCoprodObject A'.underlying.obj.obj B'.underlying.obj.obj =>
        DefinableSetCat.homFunction k u)
      (vfAllCoprodInl_desc (F.hom ≫ vfAllCoprodInl A'.underlying.obj.obj B'.underlying.obj.obj)
        (G.hom ≫ vfAllCoprodInr A'.underlying.obj.obj B'.underlying.obj.obj))
    change finiteZeroVFMap e (zeroVFCoprodLeftMap hc C A B u) =
      zeroVFCoprodLeftMap hc C A' B' (finiteZeroVFMap f.iso u) at hm
    rw [← hu,zero_vf_coprod_density_left,hm,zero_vf_coprod_density_left]
    exact f.density u
  · have hm := congrArg (fun k : B.underlying.obj.obj ⟶ vfAllCoprodObject A'.underlying.obj.obj B'.underlying.obj.obj =>
        DefinableSetCat.homFunction k v)
      (vfAllCoprodInr_desc (F.hom ≫ vfAllCoprodInl A'.underlying.obj.obj B'.underlying.obj.obj)
        (G.hom ≫ vfAllCoprodInr A'.underlying.obj.obj B'.underlying.obj.obj))
    change finiteZeroVFMap e (zeroVFCoprodRightMap hc C A B v) =
      zeroVFCoprodRightMap hc C A' B' (finiteZeroVFMap g.iso v) at hm
    rw [← hv,zero_vf_coprod_density_right,hm,zero_vf_coprod_density_right]
    exact g.density v

end IntegrationInACVF.Section7.HK
