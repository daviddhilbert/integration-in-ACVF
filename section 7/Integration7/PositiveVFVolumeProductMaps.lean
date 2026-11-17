module

public import Integration7.PositiveVFVolumeProducts
public import Section4.MapProduct
public import Section4.ProductBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual product maps and their bijectivity on mixed VF volume domains.
The Jacobian volume law is established separately. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}
variable {U U' : PositiveVFVolumeObject (M := M) S n} {V V' : PositiveVFVolumeObject (M := M) S m}

def positiveVFVolumeProductMap (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) :
    Map (U.prod V).domain (U'.prod V').domain :=
  (mixedPack U'.domain V'.domain).toImage.comp ((Map.prodMap f g).comp (mixedUnpack U.domain V.domain))

theorem positive_vf_volume_product_map_bijective
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain)
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (positiveVFVolumeProductMap f g) :=
  (mixedPackToImage_bijective U'.domain V'.domain).comp
    ((Map.prodMap_bijective f g hf hg).comp
      (Equiv.ofBijective (mixedPack U.domain V.domain).toImage (mixedPackToImage_bijective U.domain V.domain)).symm.bijective)

theorem positive_vf_volume_product_map_density
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) (u : U.domain) (v : V.domain) :
    (U'.prod V').form.value (positiveVFVolumeProductMap f g
      ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩)) =
      U'.form.value (f u) * V'.form.value (g v) := by
  simp only [positiveVFVolumeProductMap,Map.comp_apply,mixedUnpack_pack]
  exact positive_vf_volume_product_density U' V' (f u) (g v)

end IntegrationInACVF.Section7
