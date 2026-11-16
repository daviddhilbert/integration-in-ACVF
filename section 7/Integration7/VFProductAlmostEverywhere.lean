module

public import Integration7.PositiveVFVolumeProducts
public import Integration7.VFAlmostEverywhere

@[expose] public section

/-! Cartesian products retain actual almost-everywhere predicates.
The exceptional locus is the union of the two genuine product exceptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vf_almost_everywhere_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveVFVolumeObject (M := M) (C.base : Set M) m)
    {P : U.domain → Prop} {Q : V.domain → Prop}
    (hP : VFAlmostEverywhere U.domain P) (hQ : VFAlmostEverywhere V.domain Q) :
    VFAlmostEverywhere (U.prod V).domain (fun w =>
      P (Map.prodFst U.domain V.domain (mixedUnpack U.domain V.domain w)) ∧
      Q (Map.prodSnd U.domain V.domain (mixedUnpack U.domain V.domain w))) := by
  obtain ⟨E,hEU,hdE,hP⟩ := hP
  obtain ⟨F,hFV,hdF,hQ⟩ := hQ
  let ZL := mixedProductDomain (n := n+1) (m := m+1) E V.domain
  let ZR := mixedProductDomain (n := n+1) (m := m+1) U.domain F
  have hZLU : ZL.carrier ⊆ (U.prod V).domain.carrier := by
    intro p hp
    have h := (mem_mixedProductDomain E V.domain p).mp hp
    exact (mem_mixedProductDomain U.domain V.domain p).mpr ⟨hEU h.1,h.2⟩
  have hZRU : ZR.carrier ⊆ (U.prod V).domain.carrier := by
    intro p hp
    have h := (mem_mixedProductDomain U.domain F p).mp hp
    exact (mem_mixedProductDomain U.domain V.domain p).mpr ⟨h.1,hFV h.2⟩
  have hL : vfDim (rawRVSpace (M := M) 1) ZL < (n+1)+(m+1) := by
    have h := vfDim_mixed_product_le (rawRVSpace (M := M) 1) E V.domain
    have hV := vfDim_le_arity (rawRVSpace (M := M) 1) V.domain
    exact h.trans_lt (by omega)
  have hR : vfDim (rawRVSpace (M := M) 1) ZR < (n+1)+(m+1) := by
    have h := vfDim_mixed_product_le (rawRVSpace (M := M) 1) U.domain F
    have hU := vfDim_le_arity (rawRVSpace (M := M) 1) U.domain
    exact h.trans_lt (by omega)
  refine ⟨ZL.union ZR,Set.union_subset hZLU hZRU,?_,?_⟩
  · rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
    exact max_lt hL hR
  · intro w hw
    let uv := mixedUnpack U.domain V.domain w
    let a := Map.prodFst U.domain V.domain uv
    let b := Map.prodSnd U.domain V.domain uv
    have hPair := congrArg Subtype.val (mixedPack_unpack U.domain V.domain w)
    constructor
    · apply hP a
      intro ha
      have hBad : w.val ∈ ZL.carrier := by
        let z := (mixedPack E V.domain).toImage ⟨(a.val,b.val),ha,b.property⟩
        have hz : z.val = w.val := hPair
        exact hz ▸ z.property
      exact hw (Or.inl hBad)
    · apply hQ b
      intro hb
      have hBad : w.val ∈ ZR.carrier := by
        let z := (mixedPack U.domain F).toImage ⟨(a.val,b.val),a.property,hb⟩
        have hz : z.val = w.val := hPair
        exact hz ▸ z.property
      exact hw (Or.inr hBad)

end IntegrationInACVF.Section7
