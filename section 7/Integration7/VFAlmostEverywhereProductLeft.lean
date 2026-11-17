module

public import Integration7.VFVolumeProductRestrictions
public import Integration7.VFAlmostEverywhere

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An almost-everywhere predicate on the first Cartesian factor
remains so after adjoining any fixed finite tuple of auxiliary coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a b : ℕ}

theorem vf_almost_everywhere_product_left
    (A : DefSet (rawMixedSpace (M := M) n a) S)
    (B : DefSet (rawMixedSpace (M := M) m b) S)
    {P : A → Prop} (hP : VFAlmostEverywhere A P) :
    VFAlmostEverywhere (mixedProductDomain A B) (fun w => P (Map.prodFst A B (mixedUnpack A B w))) := by
  obtain ⟨E,hEA,hdE,hP⟩ := hP
  let Z := mixedProductDomain E B
  have hd : vfDim (rawRVSpace (M := M) 1) Z < n+m :=
    (vfDim_mixed_product_le (rawRVSpace (M := M) 1) E B).trans_lt
      (by have hB := vfDim_le_arity (rawRVSpace (M := M) 1) B; omega)
  refine ⟨Z,mixed_product_domain_subset hEA (Set.Subset.refl _),hd,?_⟩
  intro w hw
  let uv := mixedUnpack A B w
  let u := Map.prodFst A B uv
  let v := Map.prodSnd A B uv
  apply hP u
  intro hu
  apply hw
  let z := (mixedPack E B).toImage ⟨(u.val,v.val),hu,v.property⟩
  have he : z.val = w.val := congrArg Subtype.val (mixedPack_unpack A B w)
  exact he ▸ z.property

end IntegrationInACVF.Section7
