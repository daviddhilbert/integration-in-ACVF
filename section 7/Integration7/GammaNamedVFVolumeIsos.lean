import Integration7.VFVolumeComposition
import Integration7.VolumeDensityGraphs
import Section5.GammaInvariantLogic

/-! Gamma-definability of actual positive-degree VF volume objects and of
actual almost-everywhere VF volume isomorphisms over a Gamma base `B`.
Objects record Gamma graphs of their domains and of their volume-form graphs
(the density graph used before standard contraction); isomorphisms
record Gamma graphs of their cofull source and target and of the bijection.
Identity, inverse and composition retain these graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {k : ℕ}

/-- The graph of an actual mixed map, as a relation of Section 5 points. -/
def vfMixedMapGraph {n a m b : ℕ} {A : DefSet (rawMixedSpace (M := M) n a) S}
    {D : DefSet (rawMixedSpace (M := M) m b) S} (f : Map A D) :
    Point (M := M) n a → Point (M := M) m b → Prop :=
  fun p q => ∃ u : A, u.val = p ∧ (f u).val = q

structure VFVolumeObjectGamma (U : PositiveVFVolumeObject (M := M) S k) (B : Base (M := M)) : Prop where
  domain : GammaSetDefinable B U.domain.carrier
  densityGraph : GammaSetDefinable B (volumeDensityGraph U.form).carrier

structure VFVolumeIso.GammaDefinable {U V : PositiveVFVolumeObject (M := M) S k}
    (f : VFVolumeIso U V) (B : Base (M := M)) : Prop where
  source : GammaSetDefinable B f.source.carrier
  target : GammaSetDefinable B f.target.carrier
  graph : GammaGraphDefinable B (vfMixedMapGraph f.bijection.map)

theorem gamma_vf_identity_graph {n a : ℕ} (A : Set (Point (M := M) n a))
    (hA : GammaSetDefinable B A) :
    GammaGraphDefinable B (fun (p q : Point (M := M) n a) => p ∈ A ∧ p = q) := by
  let W := SpecialTransformations.Section5.PresentedSet.univ
    (SpecialTransformations.Section5.pointSpace (M := M) n a) B.real
  have hid := (gammaLogicInput B).real_map_graph (SpecialTransformations.Section5.Map.id W)
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA hid)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,huq⟩
    exact ⟨hp,hu.symm.trans huq⟩
  · rintro ⟨hp,rfl⟩
    exact ⟨hp,⟨p,Set.mem_univ _⟩,rfl,rfl⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem VFVolumeObjectGamma.refl_iso {U : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (hU : VFVolumeObjectGamma U B) : (VFVolumeIso.refl hc C U).GammaDefinable B := by
  refine ⟨hU.domain,hU.domain,?_⟩
  apply GammaGraphDefinable.congr (gamma_vf_identity_graph _ hU.domain)
  intro p q
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u.property,rfl⟩

theorem VFVolumeIso.GammaDefinable.symm {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeIso U V} (hf : f.GammaDefinable B) : (f.symm hc C).GammaDefinable B := by
  refine ⟨hf.target,hf.source,?_⟩
  apply GammaGraphDefinable.congr ((gammaLogicInput B).swap_graph hf.graph)
  intro p q
  constructor
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨f.bijection.map u,rfl,?_⟩
    change ((f.bijection.map.inverse f.bijection.bijective) (f.bijection.map u)).val = u.val
    rw [Map.inverse_apply]
  · rintro ⟨v,rfl,rfl⟩
    refine ⟨(f.bijection.map.inverse f.bijection.bijective) v,rfl,?_⟩
    rw [Map.apply_inverse]

theorem VFVolumeIso.GammaDefinable.trans {U V W : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    {f : VFVolumeIso U V} {g : VFVolumeIso V W} (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (f.trans hc C g).GammaDefinable B := by
  have L := gammaLogicInput B
  have hI : GammaSetDefinable B (f.target.carrier ∩ g.source.carrier) := L.inter hf.target hg.source
  have hP : GammaSetDefinable B {p | ∃ q, vfMixedMapGraph f.bijection.map p q ∧
      q ∈ f.target.carrier ∩ g.source.carrier} := by
    have h := L.image_graph (L.restrict_graph hI (L.swap_graph hf.graph))
    have he : {p | ∃ q, q ∈ f.target.carrier ∩ g.source.carrier ∧ vfMixedMapGraph f.bijection.map p q} =
        {p | ∃ q, vfMixedMapGraph f.bijection.map p q ∧ q ∈ f.target.carrier ∩ g.source.carrier} := by
      ext p
      exact exists_congr (fun q => And.comm)
    exact he ▸ h
  have hPeq : (f.trans hc C g).source.carrier = {p | ∃ q, vfMixedMapGraph f.bijection.map p q ∧
      q ∈ f.target.carrier ∩ g.source.carrier} := by
    ext p
    constructor
    · rintro ⟨u,rfl,hu⟩
      exact ⟨_,⟨u,rfl,rfl⟩,hu⟩
    · rintro ⟨q,⟨u,rfl,rfl⟩,hq⟩
      exact ⟨u,rfl,hq⟩
  have hcomp : GammaGraphDefinable B (fun p r => p ∈ {p | ∃ q, vfMixedMapGraph f.bijection.map p q ∧
      q ∈ f.target.carrier ∩ g.source.carrier} ∧
      ∃ q, vfMixedMapGraph f.bijection.map p q ∧ vfMixedMapGraph g.bijection.map q r) :=
    L.restrict_graph hP (L.comp_graph hf.graph hg.graph)
  have hgraph : GammaGraphDefinable B (vfMixedMapGraph (f.trans hc C g).bijection.map) := by
    apply GammaGraphDefinable.congr hcomp
    intro p r
    constructor
    · rintro ⟨⟨q,⟨u,rfl,rfl⟩,hq⟩,q',⟨u',hu',rfl⟩,⟨v,hv,rfl⟩⟩
      have huu : u = u' := (Subtype.ext hu').symm
      subst huu
      refine ⟨⟨u.val,⟨u,rfl,hq⟩⟩,rfl,?_⟩
      have hvv : v = ⟨(f.bijection.map u).val,hq.2⟩ := Subtype.ext hv
      subst hvv
      rfl
    · rintro ⟨w,rfl,rfl⟩
      obtain ⟨u,hu,hq⟩ := w.property
      have hw : w.val = u.val := hu.symm
      refine ⟨?_,?_⟩
      · exact ⟨_,⟨u,hw.symm,rfl⟩,hq⟩
      · refine ⟨(f.bijection.map u).val,⟨u,hw.symm,rfl⟩,⟨⟨(f.bijection.map u).val,hq.2⟩,rfl,?_⟩⟩
        have hwu : w = ⟨u.val,⟨u,rfl,hq⟩⟩ := Subtype.ext hw
        subst hwu
        rfl
  refine ⟨hPeq ▸ hP,?_,hgraph⟩
  have h := L.image_graph hgraph
  have he : {r | ∃ p, vfMixedMapGraph (f.trans hc C g).bijection.map p r} = (f.trans hc C g).target.carrier := by
    ext r
    constructor
    · rintro ⟨p,w,rfl,rfl⟩
      exact (((f.trans hc C g).bijection.map w).property)
    · intro hr
      obtain ⟨w,hw⟩ := (f.trans hc C g).bijection.bijective.2 ⟨r,hr⟩
      exact ⟨w.val,w,rfl,congrArg Subtype.val hw⟩
  exact he ▸ h

end IntegrationInACVF.Section7
