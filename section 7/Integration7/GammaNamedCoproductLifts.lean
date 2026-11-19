import Integration7.GammaNamedElementaryLifts
import Integration7.FixedVFVolumeCoproductIsomorphisms
import Integration7.VolumeLiftCoproductBijections
import Integration7.GammaRVLabelIdentity
import Integration7.GammaNamedFormGraphs
import Section9.GammaPointMaps

/-! Gamma graphs of coproduct constructions on VF volume objects: tagging,
unions of maps, coproducts of bijections and isomorphisms, and the
identification of the coproduct of lifts with the lift of the coproduct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {k : ℕ}

/-- Left tagging of the RV labels, as a Gamma relation. -/
theorem gamma_vf_left_tag_relation {n a b : ℕ} :
    GammaGraphDefinable B (fun (p : Point (M := M) n a) (q : Point (M := M) n (1+(a+b))) =>
      q = (p.1, rvLeftTag (M := M) b p.2)) := by
  have L := gammaLogicInput B
  have hRV := (gamma_rv_left_tag B a b).preimage_maps
    (SpecialTransformations.Section9.GammaLift.pointCoordinateMap (Fin.elim0 : Fin 0 → Fin n) id B.real)
    (SpecialTransformations.Section9.GammaLift.pointCoordinateMap (Fin.elim0 : Fin 0 → Fin n) id B.real)
  have hVF := L.comp_graph
    (SpecialTransformations.Section9.GammaLift.gamma_coordinate_graph (B := B) (n := n) (m := a) (u := n) (w := 0) id Fin.elim0)
    (L.swap_graph (SpecialTransformations.Section9.GammaLift.gamma_coordinate_graph (B := B) (n := n) (m := 1+(a+b)) (u := n) (w := 0) id Fin.elim0))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (SpecialTransformations.Section5.GammaGraphDefinable.inter hVF hRV)
  intro p q
  constructor
  · rintro ⟨⟨z, hz, hz'⟩, hr⟩
    refine Prod.ext ?_ ?_
    · have := congrArg Prod.fst (hz.symm.trans hz')
      exact this.symm
    · exact hr.symm
  · intro h
    subst h
    exact ⟨⟨_, rfl, Prod.ext rfl (funext (fun i => Fin.elim0 i))⟩, rfl⟩

theorem gamma_vf_right_tag_relation {n a b : ℕ} :
    GammaGraphDefinable B (fun (p : Point (M := M) n b) (q : Point (M := M) n (1+(a+b))) =>
      q = (p.1, rvRightTag (M := M) a p.2)) := by
  have L := gammaLogicInput B
  have hRV := (gamma_rv_right_tag B a b).preimage_maps
    (SpecialTransformations.Section9.GammaLift.pointCoordinateMap (Fin.elim0 : Fin 0 → Fin n) id B.real)
    (SpecialTransformations.Section9.GammaLift.pointCoordinateMap (Fin.elim0 : Fin 0 → Fin n) id B.real)
  have hVF := L.comp_graph
    (SpecialTransformations.Section9.GammaLift.gamma_coordinate_graph (B := B) (n := n) (m := b) (u := n) (w := 0) id Fin.elim0)
    (L.swap_graph (SpecialTransformations.Section9.GammaLift.gamma_coordinate_graph (B := B) (n := n) (m := 1+(a+b)) (u := n) (w := 0) id Fin.elim0))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (SpecialTransformations.Section5.GammaGraphDefinable.inter hVF hRV)
  intro p q
  constructor
  · rintro ⟨⟨z, hz, hz'⟩, hr⟩
    refine Prod.ext ?_ ?_
    · have := congrArg Prod.fst (hz.symm.trans hz')
      exact this.symm
    · exact hr.symm
  · intro h
    subst h
    exact ⟨⟨_, rfl, Prod.ext rfl (funext (fun i => Fin.elim0 i))⟩, rfl⟩

/-- A VF volume bijection with a Gamma graph. -/
def VFBijGamma {U V : PositiveVFVolumeObject (M := M) S k} (f : VFVolumeBijection U V)
    (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B (vfMixedMapGraph f.map)

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem VFBijGamma.trans {U V W : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeBijection U V} {g : VFVolumeBijection V W} (hf : VFBijGamma f B) (hg : VFBijGamma g B) :
    VFBijGamma (f.trans hc C g) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨y, ⟨x, rfl, rfl⟩, x', hx', rfl⟩
    have : x' = f.map x := Subtype.ext hx'
    subst this
    exact ⟨x, rfl, rfl⟩
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨_, ⟨x, rfl, rfl⟩, f.map x, rfl, rfl⟩

theorem VFBijGamma.symm {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeBijection U V} (hf : VFBijGamma f B) : VFBijGamma (f.symm hc C) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph hf)
  intro p q
  constructor
  · rintro ⟨u, rfl, rfl⟩
    refine ⟨f.map u, rfl, ?_⟩
    change ((f.map.inverse f.bijective) (f.map u)).val = u.val
    rw [Map.inverse_apply]
  · rintro ⟨v, rfl, rfl⟩
    refine ⟨(f.map.inverse f.bijective) v, rfl, ?_⟩
    rw [Map.apply_inverse]

theorem vf_left_tag_bijection_gamma (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (b : ℕ)
    (hU : GammaSetDefinable B U.domain.carrier) : VFBijGamma (vfVolumeLeftTagBijection hc C U b) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).restrict_graph hU gamma_vf_left_tag_relation)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl, rfl⟩
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨x.property, rfl⟩

theorem vf_right_tag_bijection_gamma (V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (a : ℕ)
    (hV : GammaSetDefinable B V.domain.carrier) : VFBijGamma (vfVolumeRightTagBijection hc C V a) B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput B).restrict_graph hV gamma_vf_right_tag_relation)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl, rfl⟩
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨x.property, rfl⟩

theorem union_mixed_map_gamma {n a b : ℕ}
    {A A' : DefSet (rawMixedSpace (M := M) n a) S} {D D' : DefSet (rawMixedSpace (M := M) n b) S}
    (hAA' : Disjoint A.carrier A'.carrier) (f : Map A D) (g : Map A' D')
    (hf : GammaGraphDefinable B (vfMixedMapGraph f)) (hg : GammaGraphDefinable B (vfMixedMapGraph g)) :
    GammaGraphDefinable B (vfMixedMapGraph (unionMixedMap f g)) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput B).union_graph hf hg)
  intro p q
  constructor
  · rintro (⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
    · refine ⟨⟨x.val, Or.inl x.property⟩, rfl, ?_⟩
      simp [unionMixedMap, Map.union, x.property]
      rfl
    · refine ⟨⟨x.val, Or.inr x.property⟩, rfl, ?_⟩
      have hx : x.val ∉ A.carrier := fun h => Set.disjoint_left.mp hAA' h x.property
      simp [unionMixedMap, Map.union, hx]
      rfl
  · rintro ⟨x, rfl, rfl⟩
    by_cases hx : x.val ∈ A.carrier
    · refine Or.inl ⟨⟨x.val, hx⟩, rfl, ?_⟩
      simp [unionMixedMap, Map.union, hx]
      rfl
    · refine Or.inr ⟨⟨x.val, x.property.resolve_left hx⟩, rfl, ?_⟩
      simp [unionMixedMap, Map.union, hx]
      rfl

theorem VFBijGamma.coprod {U U' V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeBijection U U'} {g : VFVolumeBijection V V'} (hf : VFBijGamma f B) (hg : VFBijGamma g B)
    (hU : GammaSetDefinable B U.domain.carrier) (hV : GammaSetDefinable B V.domain.carrier)
    (hU' : GammaSetDefinable B U'.domain.carrier) (hV' : GammaSetDefinable B V'.domain.carrier) :
    VFBijGamma (f.coprod hc C g) B := by
  have hL := ((vf_left_tag_bijection_gamma hc C U V.arity hU).symm hc C).trans hc C
    (hf.trans hc C (vf_left_tag_bijection_gamma hc C U' V'.arity hU'))
  have hR := ((vf_right_tag_bijection_gamma hc C V U.arity hV).symm hc C).trans hc C
    (hg.trans hc C (vf_right_tag_bijection_gamma hc C V' U'.arity hV'))
  exact union_mixed_map_gamma (fixed_vf_tagged_images_disjoint U.domain V.domain) _ _ hL hR

theorem vf_coprod_domain_gamma {U V : PositiveVFVolumeObject (M := M) S k}
    (hU : GammaSetDefinable B U.domain.carrier) (hV : GammaSetDefinable B V.domain.carrier) :
    GammaSetDefinable B (U.coprod V).domain.carrier := by
  have L := gammaLogicInput B
  have h := L.union (L.image_graph (L.restrict_graph hU (gamma_vf_left_tag_relation (B := B) (b := V.arity))))
    (L.image_graph (L.restrict_graph hV (gamma_vf_right_tag_relation (B := B) (a := U.arity))))
  have he : (U.coprod V).domain.carrier =
      {q | ∃ p, p ∈ U.domain.carrier ∧ q = (p.1, rvLeftTag (M := M) V.arity p.2)} ∪
      {q | ∃ p, p ∈ V.domain.carrier ∧ q = (p.1, rvRightTag (M := M) U.arity p.2)} := by
    ext q
    constructor
    · rintro (⟨u, hu⟩ | ⟨v, hv⟩)
      · exact Or.inl ⟨u.val, u.property, hu.symm⟩
      · exact Or.inr ⟨v.val, v.property, hv.symm⟩
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact Or.inl ⟨⟨p, hp⟩, rfl⟩
      · exact Or.inr ⟨⟨p, hp⟩, rfl⟩
  rw [he]
  exact h

theorem vf_identity_map_gamma {n a : ℕ} {A D : DefSet (rawMixedSpace (M := M) n a) S}
    (f : Map A D) (hid : ∀ x, (f x).val = x.val)
    (hU : GammaSetDefinable B A.carrier) : GammaGraphDefinable B (vfMixedMapGraph f) := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hU)
  intro p q
  constructor
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl, hid _⟩
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨x.property, (hid x).symm⟩

theorem VFVolumeIso.GammaDefinable.coprod {U U' V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeIso U U'} {g : VFVolumeIso V V'} (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (f.coprod hc C g).GammaDefinable B := by
  have hP := vf_coprod_domain_gamma (U := U.restrict f.source f.source_subset)
    (V := V.restrict g.source g.source_subset) hf.source hg.source
  have hQ := vf_coprod_domain_gamma (U := U'.restrict f.target f.target_subset)
    (V := V'.restrict g.target g.target_subset) hf.target hg.target
  refine ⟨hP, hQ, ?_⟩
  have h₁ := (show VFBijGamma (vfVolumeCoprodRestrictionBijection hc C U V f.source g.source
    f.source_subset g.source_subset) B from vf_identity_map_gamma _ (fun _ => rfl) hP).symm hc C
  have h₂ : VFBijGamma (f.bijection.coprod hc C g.bijection) B :=
    VFBijGamma.coprod hc C hf.graph hg.graph hf.source hg.source hf.target hg.target
  have h₃ : VFBijGamma (vfVolumeCoprodRestrictionBijection hc C U' V' f.target g.target
    f.target_subset g.target_subset) B := vf_identity_map_gamma _ (fun _ => rfl) hQ
  exact h₁.trans hc C (h₂.trans hc C h₃)

theorem volume_lift_coprod_iso_gamma (hGC : B.real ⊆ (C.base : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (volumeLiftCoprodIso hc C U V).GammaDefinable B := by
  have hs := vf_coprod_domain_gamma (U := rvVolumeLift U) (V := rvVolumeLift V)
    (gamma_rv_lift_carrier hc C hGC U hU) (gamma_rv_lift_carrier hc C hGC V hV)
  have ht := gamma_rv_lift_carrier hc C hGC (U.coprod V) (hU.coprod hV)
  exact ⟨hs, ht, vf_identity_map_gamma (volumeLiftCoprodBijection hc C U V).map (fun _ => rfl) hs⟩

end IntegrationInACVF.Section7
