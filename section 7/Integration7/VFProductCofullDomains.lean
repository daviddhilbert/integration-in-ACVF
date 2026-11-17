module

public import Integration7.VFVolumeProductRestrictions
public import Integration7.VFProductAlmostEverywhere
public import Integration7.VFCofullSubdomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The genuine product of two cofull definable subdomains is cofull. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vf_volume_product_cofull
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveVFVolumeObject (M := M) (C.base : Set M) m)
    {L : DefSet (rawMixedSpace (M := M) (n+1) U.arity) (C.base : Set M)}
    {K : DefSet (rawMixedSpace (M := M) (m+1) V.arity) (C.base : Set M)}
    (hL : VFCofull U.domain L) (hK : VFCofull V.domain K) :
    VFCofull (U.prod V).domain (mixedProductDomain (n := n+1) (m := m+1) L K) := by
  have hPL : VFAlmostEverywhere U.domain (fun u => u.val ∈ L.carrier) := by
    refine ⟨U.domain.sdiff L,Set.diff_subset,hL.small,?_⟩
    intro u hu
    by_contra h
    exact hu ⟨u.property,h⟩
  have hPK : VFAlmostEverywhere V.domain (fun v => v.val ∈ K.carrier) := by
    refine ⟨V.domain.sdiff K,Set.diff_subset,hK.small,?_⟩
    intro v hv
    by_contra h
    exact hv ⟨v.property,h⟩
  obtain ⟨Z,hZ,hdZ,hP⟩ := vf_almost_everywhere_product hc C U V hPL hPK
  refine ⟨mixed_product_domain_subset hL.subset hK.subset,
    (vfDim_mono_same_arity ?_).trans_lt hdZ⟩
  intro p hp
  by_contra hz
  have h := hP ⟨p,hp.1⟩ hz
  let uv := mixedUnpack U.domain V.domain ⟨p,hp.1⟩
  let u := Map.prodFst U.domain V.domain uv
  let v := Map.prodSnd U.domain V.domain uv
  apply hp.2
  let z := (mixedPack L K).toImage ⟨(u.val,v.val),h.1,h.2⟩
  have he : z.val = p := congrArg Subtype.val (mixedPack_unpack U.domain V.domain ⟨p,hp.1⟩)
  exact he ▸ z.property

end IntegrationInACVF.Section7
