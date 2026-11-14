import Integration7.VFAlmostEverywhere
import Integration7.DefinableMapPreimages

/-! Definable subdomains with VF-small complements, and their actual
preimages and images under definable bijections. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

theorem vfDim_mono_same_arity
    {A B : DefSet (rawMixedSpace (M := M) n a) S} (hAB : A.carrier ⊆ B.carrier) :
    vfDim (rawRVSpace (M := M) 1) A ≤ vfDim (rawRVSpace (M := M) 1) B := by
  have hinj : Function.Injective (Map.inclusion hAB) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : B => z.val) he)
  exact vfDim_le_of_finite_map _ (Map.inclusion hAB) (Map.finiteFibres_of_injective hinj)

structure VFCofull (A L : DefSet (rawMixedSpace (M := M) n a) S) : Prop where
  subset : L.carrier ⊆ A.carrier
  small : vfDim (rawRVSpace (M := M) 1) (A.sdiff L) < n

theorem VFCofull.trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A L K : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    (hL : VFCofull A L) (hK : VFCofull L K) : VFCofull A K := by
  refine ⟨hK.subset.trans hL.subset, ?_⟩
  have hsub : (A.sdiff K).carrier ⊆ ((A.sdiff L).union (L.sdiff K)).carrier := by
    intro x hx
    by_cases hxL : x ∈ L.carrier
    · exact Or.inr ⟨hxL, hx.2⟩
    · exact Or.inl ⟨hx.1, hxL⟩
  apply (vfDim_mono_same_arity hsub).trans_lt
  rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
  exact max_lt hL.small hK.small

theorem VFCofull.inter_right
    {A L K : DefSet (rawMixedSpace (M := M) n a) S}
    (hK : VFCofull A K) (hL : L.carrier ⊆ A.carrier) : VFCofull L (L.inter K) := by
  refine ⟨Set.inter_subset_left, (vfDim_mono_same_arity ?_).trans_lt hK.small⟩
  intro x hx
  exact ⟨hL hx.1, fun hxK => hx.2 ⟨hx.1, hxK⟩⟩

theorem VFCofull.inter_left
    {A L K : DefSet (rawMixedSpace (M := M) n a) S}
    (hL : VFCofull A L) (hK : K.carrier ⊆ A.carrier) : VFCofull K (L.inter K) := by
  refine ⟨Set.inter_subset_right, (vfDim_mono_same_arity ?_).trans_lt hL.small⟩
  intro x hx
  exact ⟨hK hx.1, fun hxL => hx.2 ⟨hxL, hx.1⟩⟩

theorem VFCofull.preimage
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B K : DefSet (rawMixedSpace (M := M) n b) S}
    (F : Map A B) (hF : Function.Injective F) (hK : VFCofull B K) :
    VFCofull A (definableMapPreimage F K) := by
  refine ⟨definableMapPreimage_subset F K, ?_⟩
  let L := definableMapPreimage F K
  let hEA : (A.sdiff L).carrier ⊆ A.carrier := Set.diff_subset
  let G : Map (A.sdiff L) (B.sdiff K) := (F.restrict hEA).corestrict (by
    intro x
    refine ⟨(F ⟨x.val, hEA x.property⟩).property, ?_⟩
    exact fun hx => x.property.2 ((mem_definableMapPreimage F K ⟨x.val, hEA x.property⟩).mpr hx))
  have hG : Function.Injective G := by
    intro x y he
    have hFxy := hF (Subtype.ext (congrArg (fun z : B.sdiff K => z.val) he))
    exact Subtype.ext (congrArg (fun z : A => z.val) hFxy)
  exact (vfDim_le_of_finite_map _ G (Map.finiteFibres_of_injective hG)).trans_lt hK.small

theorem VFCofull.image
    {A L : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (F : Map A B) (hF : Function.Bijective F) (hL : VFCofull A L) :
    VFCofull B (F.restrict hL.subset).image := by
  let Q := (F.restrict hL.subset).image
  have hQB : Q.carrier ⊆ B.carrier := by
    rintro x ⟨p, rfl⟩
    exact (F ⟨p.val, hL.subset p.property⟩).property
  refine ⟨hQB, ?_⟩
  let hEB : (B.sdiff Q).carrier ⊆ B.carrier := Set.diff_subset
  let G : Map (B.sdiff Q) (A.sdiff L) :=
    ((F.inverse hF).restrict hEB).corestrict (by
      intro x
      let b : B := ⟨x.val, hEB x.property⟩
      let p := F.inverse hF b
      refine ⟨p.property, ?_⟩
      intro hpL
      apply x.property.2
      refine ⟨⟨p.val, hpL⟩, ?_⟩
      exact congrArg (fun b : B => b.val) (Map.apply_inverse F hF b))
  have hG : Function.Injective G := by
    intro x y he
    have hxy : F.inverse hF ⟨x.val, hEB x.property⟩ = F.inverse hF ⟨y.val, hEB y.property⟩ :=
      Subtype.ext (congrArg (fun z : A.sdiff L => z.val) he)
    have hb := congrArg F hxy
    simp only [Map.apply_inverse] at hb
    exact Subtype.ext (congrArg (fun b : B => b.val) hb)
  exact (vfDim_le_of_finite_map _ G (Map.finiteFibres_of_injective hG)).trans_lt hL.small

end IntegrationInACVF.Section7
