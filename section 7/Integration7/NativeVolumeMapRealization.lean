module

public import Integration7.NativeVolumeDomains

@[expose] public section

/-! Actual raw mixed maps in the shared language become native Section 5
maps without changing their point functions or real parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m a b : ℕ}

set_option maxHeartbeats 1600000 in
def nativeMixedVolumeMap
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) m b) S} (f : Map A B) :
    SpecialTransformations.Section5.Map (nativeMixedVolumeDomain hc A) (nativeMixedVolumeDomain hc B) := by
  let N := @CanonicalStructure.normalize M sM
  letI : LRV.Structure M := sM
  let H := (rawMixedSpace (M := M) n a).relation (rawMixedSpace (M := M) m b) f.graph
  have hH : @Set.Definable M S LRV N ((Fin n ⊕ Fin a) ⊕ (Fin m ⊕ Fin b)) H :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M S LRV I ((Fin n ⊕ Fin a) ⊕ (Fin m ⊕ Fin b)) H)
      (normalize_eq_of_isCanonical hc).symm) f.graph_definable
  let AN := nativeMixedVolumeDomain hc A
  let BN := nativeMixedVolumeDomain hc B
  let amap := SpecialTransformations.Section5.Map.toImage (SpecialTransformations.Section5.rawPointMap AN)
  let bmap := SpecialTransformations.Section5.Map.toImage (SpecialTransformations.Section5.rawPointMap BN)
  let DB := SpecialTransformations.Section5.Map.image (SpecialTransformations.Section5.rawPointMap BN)
  let PA := SpecialTransformations.Section5.rawPointSpace (M := M) n a
  let PB := SpecialTransformations.Section5.rawPointSpace (M := M) m b
  let R (x : @Space.Carrier LRV M N PA) (y : @Space.Carrier LRV M N PB) :=
    ∃ u : A, u.val = x ∧ (f u).val = y
  have hR : @Space.RelationDefinable LRV M N PA PB S R := hH
  letI : LRV.Structure M := N
  have hb : Function.Bijective bmap := by
    constructor
    · intro p q h
      have he := congrArg (fun v : DB => v.val) h
      exact Subtype.ext he
    · rintro ⟨p,q,rfl⟩
      exact ⟨q,rfl⟩
  let bi := SpecialTransformations.DefinableGeometry.Map.inverse bmap hb
  have hbi (v : DB) : (bi v).val = v.val :=
    congrArg (fun t : DB => t.val) (SpecialTransformations.DefinableGeometry.Map.apply_inverse bmap hb v)
  have hcomp := Space.RelationDefinable.comp _ _ _
    (Space.RelationDefinable.comp _ _ _ amap.graph_definable hR) bi.graph_definable
  refine @Map.mk LRV M N _ _ S _ _ (fun p => f ⟨p.val,p.property⟩) ?_
  apply Space.RelationDefinable.congr _ _ hcomp
  intro x y
  constructor
  · rintro ⟨r,⟨s,⟨p,hp,hs⟩,u,hu,hfr⟩,v,hv,hq⟩
    have hup : u = (⟨p.val,p.property⟩ : A) := Subtype.ext (hu.trans hs.symm)
    refine ⟨p,hp,?_⟩
    rw [← hup]
    exact hfr.trans (hv.symm.trans ((hbi v).symm.trans hq))
  · rintro ⟨p,hp,hq⟩
    let u : A := ⟨p.val,p.property⟩
    let v : BN := ⟨(f u).val,(f u).property⟩
    refine ⟨(f u).val,⟨p.val,⟨p,hp,rfl⟩,u,rfl,rfl⟩,bmap v,rfl,?_⟩
    exact (congrArg Subtype.val (SpecialTransformations.DefinableGeometry.Map.inverse_apply bmap hb v)).trans hq

theorem native_mixed_volume_map_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) m b) S} (f : Map A B)
    (p : nativeMixedVolumeDomain hc A) :
    (nativeMixedVolumeMap hc f p).val = (f ⟨p.val,p.property⟩).val := rfl

theorem native_mixed_volume_map_bijective
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) m b) S} (f : Map A B)
    (hf : Function.Bijective f) : Function.Bijective (nativeMixedVolumeMap hc f) := hf

end IntegrationInACVF.Section7
