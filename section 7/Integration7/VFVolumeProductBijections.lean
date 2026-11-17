module

public import Integration7.MixedVFProductJacobians
public import Integration7.VFProductAlmostEverywhere
public import Integration7.VFVolumeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Cartesian products of actual full VF volume bijections preserve
the product volume, using the actual mixed Jacobian and small exceptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
variable {C : BaseContext M}
variable {U U' : PositiveVFVolumeObject (M := M) (C.base : Set M) n}
variable {V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) m}

theorem preserves_vf_volume_product
    (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain)
    (hf : PreservesVFVolume U.form U'.form f) (hg : PreservesVFVolume V.form V'.form g) :
    PreservesVFVolume (U.prod V).form (U'.prod V').form (positiveVFVolumeProductMap f g) := by
  apply (vf_almost_everywhere_product hc C U V hf hg).mono
  intro w h
  let uv := mixedUnpack U.domain V.domain w
  let u := Map.prodFst U.domain V.domain uv
  let v := Map.prodSnd U.domain V.domain uv
  obtain ⟨J,hJ,hU⟩ := h.1
  obtain ⟨K,hK,hV⟩ := h.2
  have hw : (mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩ = w :=
    mixedPack_unpack U.domain V.domain w
  refine ⟨J*K,hw ▸ has_mixed_vf_jacobian_product f g u v J K hJ hK,?_⟩
  calc
    (U.prod V).form.value w = U.form.value u * V.form.value v := by
      rw [← hw]
      exact positive_vf_volume_product_density U V u v
    _ = (U'.form.value (f u) * CanonicalRV.encodedRv J) *
        (V'.form.value (g v) * CanonicalRV.encodedRv K) := congrArg₂ (·*·) hU hV
    _ = (U'.prod V').form.value (positiveVFVolumeProductMap f g w) * CanonicalRV.encodedRv (J*K) := by
      have hDensity := positive_vf_volume_product_map_density f g u v
      rw [hw] at hDensity
      rw [hDensity,RVOperations.rv_mul]
      ac_rfl

def VFVolumeBijection.prod
    (hc : CanonicalStructure.IsCanonical (M := M))
    (f : VFVolumeBijection U U') (g : VFVolumeBijection V V') : VFVolumeBijection (U.prod V) (U'.prod V') where
  map := positiveVFVolumeProductMap f.map g.map
  bijective := positive_vf_volume_product_map_bijective f.map g.map f.bijective g.bijective
  preserves := preserves_vf_volume_product hc f.map g.map f.preserves g.preserves

end IntegrationInACVF.Section7
