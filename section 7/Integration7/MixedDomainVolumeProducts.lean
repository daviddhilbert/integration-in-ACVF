module

public import Integration7.MixedDomainProductAlmostEverywhere
public import Integration7.MixedDomainProductJacobians
public import Integration7.VolumeFormProducts
public import Integration7.VFVolumeBijections

@[expose] public section

/-! Product volume preservation for raw mixed domains. Neither factor is
required to have finite RV fibres; finiteness can be imposed after restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m a b a' b' : ℕ}
variable {U : DefSet (rawMixedSpace (M := M) n a) S}
variable {V : DefSet (rawMixedSpace (M := M) m b) S}

def mixedDomainProductVolumeForm (ω : VolumeForm U) (η : VolumeForm V) :
    VolumeForm (mixedProductDomain U V) :=
  (ω.prod η).pullback (mixedUnpack U V)

theorem mixed_domain_product_volume_value (ω : VolumeForm U) (η : VolumeForm V)
    (u : U) (v : V) :
    (mixedDomainProductVolumeForm ω η).value
      ((mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) = ω.value u * η.value v := by
  change (ω.prod η).value (mixedUnpack U V
    ((mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩)) = _
  rw [mixedUnpack_pack]
  rfl

theorem preserves_vf_volume_mixed_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {V : DefSet (rawMixedSpace (M := M) m b) (C.base : Set M)}
    {U' : DefSet (rawMixedSpace (M := M) n a') (C.base : Set M)}
    {V' : DefSet (rawMixedSpace (M := M) m b') (C.base : Set M)}
    (ω : VolumeForm U) (η : VolumeForm V) (ω' : VolumeForm U') (η' : VolumeForm V')
    (f : Map U U') (g : Map V V')
    (hf : PreservesVFVolume ω ω' f) (hg : PreservesVFVolume η η' g) :
    PreservesVFVolume (mixedDomainProductVolumeForm ω η) (mixedDomainProductVolumeForm ω' η')
      (mixedDomainProductMap f g) := by
  apply (vf_almost_everywhere_mixed_product hc C U V hf hg).mono
  intro w h
  let uv := mixedUnpack U V w
  let u := Map.prodFst U V uv
  let v := Map.prodSnd U V uv
  obtain ⟨J,hJ,hU⟩ := h.1
  obtain ⟨K,hK,hV⟩ := h.2
  have hw : (mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩ = w :=
    mixedPack_unpack U V w
  refine ⟨J*K,hw ▸ has_mixed_vf_jacobian_domain_product f g u v J K hJ hK,?_⟩
  calc
    (mixedDomainProductVolumeForm ω η).value w = ω.value u * η.value v := rfl
    _ = (ω'.value (f u) * CanonicalRV.encodedRv J) *
        (η'.value (g v) * CanonicalRV.encodedRv K) := congrArg₂ (·*·) hU hV
    _ = (mixedDomainProductVolumeForm ω' η').value (mixedDomainProductMap f g w) *
        CanonicalRV.encodedRv (J*K) := by
      rw [← hw,mixed_domain_product_map_pair,mixed_domain_product_volume_value,RVOperations.rv_mul]
      ac_rfl

end IntegrationInACVF.Section7
