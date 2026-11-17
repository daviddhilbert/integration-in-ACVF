module

public import Integration7.PositiveVFVolumeProducts
public import Integration7.VFAlmostEverywhere

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Raw mixed-domain products retain actual almost-everywhere predicates,
without a finite-RV-fibre assumption on either factor.
The exceptional locus is the union of the two genuine product exceptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m a b : ℕ}

theorem vf_almost_everywhere_mixed_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (V : DefSet (rawMixedSpace (M := M) m b) (C.base : Set M))
    {P : U → Prop} {Q : V → Prop}
    (hP : VFAlmostEverywhere U P) (hQ : VFAlmostEverywhere V Q) :
    VFAlmostEverywhere (mixedProductDomain U V) (fun w =>
      P (Map.prodFst U V (mixedUnpack U V w)) ∧
      Q (Map.prodSnd U V (mixedUnpack U V w))) := by
  obtain ⟨E,hEU,hdE,hP⟩ := hP
  obtain ⟨F,hFV,hdF,hQ⟩ := hQ
  let ZL := mixedProductDomain (n := n) (m := m) E V
  let ZR := mixedProductDomain (n := n) (m := m) U F
  have hZLU : ZL.carrier ⊆ (mixedProductDomain U V).carrier := by
    intro p hp
    have h := (mem_mixedProductDomain E V p).mp hp
    exact (mem_mixedProductDomain U V p).mpr ⟨hEU h.1,h.2⟩
  have hZRU : ZR.carrier ⊆ (mixedProductDomain U V).carrier := by
    intro p hp
    have h := (mem_mixedProductDomain U F p).mp hp
    exact (mem_mixedProductDomain U V p).mpr ⟨h.1,hFV h.2⟩
  have hL : vfDim (rawRVSpace (M := M) 1) ZL < n+m := by
    have h := vfDim_mixed_product_le (rawRVSpace (M := M) 1) E V
    have hV := vfDim_le_arity (rawRVSpace (M := M) 1) V
    exact h.trans_lt (by omega)
  have hR : vfDim (rawRVSpace (M := M) 1) ZR < n+m := by
    have h := vfDim_mixed_product_le (rawRVSpace (M := M) 1) U F
    have hU := vfDim_le_arity (rawRVSpace (M := M) 1) U
    exact h.trans_lt (by omega)
  refine ⟨ZL.union ZR,Set.union_subset hZLU hZRU,?_,?_⟩
  · rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
    exact max_lt hL hR
  · intro w hw
    let uv := mixedUnpack U V w
    let a := Map.prodFst U V uv
    let b := Map.prodSnd U V uv
    have hPair := congrArg Subtype.val (mixedPack_unpack U V w)
    constructor
    · apply hP a
      intro ha
      have hBad : w.val ∈ ZL.carrier := by
        let z := (mixedPack E V).toImage ⟨(a.val,b.val),ha,b.property⟩
        have hz : z.val = w.val := hPair
        exact hz ▸ z.property
      exact hw (Or.inl hBad)
    · apply hQ b
      intro hb
      have hBad : w.val ∈ ZR.carrier := by
        let z := (mixedPack U F).toImage ⟨(a.val,b.val),a.property,hb⟩
        have hz : z.val = w.val := hPair
        exact hz ▸ z.property
      exact hw (Or.inr hBad)

end IntegrationInACVF.Section7
