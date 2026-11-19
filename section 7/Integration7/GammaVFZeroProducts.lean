import Integration7.GammaFunZeroPositiveLinearity
import Integration7.HKWeightedVFZeroIsomorphisms
import Integration7.HKWeightedZeroLiftProducts
import Integration7.MixedDomainProductJacobians

/-! **Gamma weighted degree-zero factors of VF volume objects.** The weighted product
`X ⊗ Z` of a Gamma positive VF volume object with a Gamma degree-zero RV object (the raw
`HK.positiveVFZeroProduct`) is Gamma; the lift of a weighted positive-zero product is Gamma
isomorphic to the weighted product of the lift; and Gamma standard contractions of `X ⊗ Z` are
common-context equivalent to the positive-zero products of contractions of `X` with `Z`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace mixedProductDomain mixedPack mixedUnpack mem_mixedProductDomain rvLift)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n m a b a' b' : ℕ}

theorem mixed_domain_product_map_value {A : DefSet (rawMixedSpace (M := M) n a) S} {B : DefSet (rawMixedSpace (M := M) m b) S}
    {A' : DefSet (rawMixedSpace (M := M) n a') S} {B' : DefSet (rawMixedSpace (M := M) m b') S}
    (f : Map A A') (g : Map B B') (w : mixedProductDomain A B) (u : A) (v : B)
    (hu : u.val = (w.val.1 ∘ Fin.castAdd m,w.val.2 ∘ Fin.castAdd b))
    (hv : v.val = (w.val.1 ∘ Fin.natAdd n,w.val.2 ∘ Fin.natAdd a)) :
    (mixedDomainProductMap f g w).val = (Fin.append (f u).val.1 (g v).val.1,Fin.append (f u).val.2 (g v).val.2) := by
  have hw : w = (mixedPack A B).toImage ⟨(u.val,v.val),u.property,v.property⟩ := by
    apply Subtype.ext
    change w.val = (Fin.append u.val.1 v.val.1,Fin.append u.val.2 v.val.2)
    rw [hu,hv]
    refine Prod.ext ?_ ?_
    · exact Fin.append_castAdd_natAdd.symm
    · exact Fin.append_castAdd_natAdd.symm
  subst hw
  rw [mixed_domain_product_map_pair]
  rfl

theorem gamma_mixed_domain_product_map_graph {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) m b) S}
    {A' : DefSet (rawMixedSpace (M := M) n a') S} {B' : DefSet (rawMixedSpace (M := M) m b') S}
    {f : Map A A'} {g : Map B B'}
    (hf : GammaGraphDefinable G (vfMixedMapGraph f)) (hg : GammaGraphDefinable G (vfMixedMapGraph g))
    (hA : GammaSetDefinable G A.carrier) (hB : GammaSetDefinable G B.carrier) :
    GammaGraphDefinable G (vfMixedMapGraph (mixedDomainProductMap f g)) := by
  have L := gammaLogicInput G
  have hF := hf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd m : Fin n → Fin (n+m)) (Fin.castAdd b : Fin a → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (Fin.castAdd m : Fin n → Fin (n+m)) (Fin.castAdd b' : Fin a' → Fin (a'+b')) G.real)
  have hG := hg.preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd n : Fin m → Fin (n+m)) (Fin.natAdd a : Fin b → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (Fin.natAdd n : Fin m → Fin (n+m)) (Fin.natAdd a' : Fin b' → Fin (a'+b')) G.real)
  have hR := L.restrict_graph (gamma_mixed_product_domain hA hB) (hF.inter hG)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    rw [mixed_domain_product_map_value f g ⟨p,hp⟩ u v hu hv,hfu,hgv]
    refine Prod.ext ?_ ?_
    · exact Fin.append_castAdd_natAdd
    · exact Fin.append_castAdd_natAdd
  · rintro ⟨w,rfl,rfl⟩
    have h := (mem_mixedProductDomain A B w.val).mp w.property
    have hval := mixed_domain_product_map_value f g w ⟨_,h.1⟩ ⟨_,h.2⟩ rfl rfl
    refine ⟨w.property,⟨⟨_,h.1⟩,rfl,?_⟩,⟨⟨_,h.2⟩,rfl,?_⟩⟩
    · rw [hval]
      refine Prod.ext ?_ ?_
      · funext i
        exact (Fin.append_left _ _ i).symm
      · funext i
        exact (Fin.append_left _ _ i).symm
    · rw [hval]
      refine Prod.ext ?_ ?_
      · funext i
        exact (Fin.append_right _ _ i).symm
      · funext i
        exact (Fin.append_right _ _ i).symm

section WeightedZero
variable {X : PositiveVFVolumeObject (M := M) S n} {Z : HK.ZeroRVVolumeObject (M := M) S}

theorem weighted_vf_zero_density_point (X : PositiveVFVolumeObject (M := M) S n) (Z : HK.ZeroRVVolumeObject (M := M) S)
    (p : (HK.positiveVFZeroProduct X Z).domain) :
    (HK.positiveVFZeroProduct X Z).form.value p =
      X.form.value ⟨_,((mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj) p.val).mp
        p.property).1⟩ *
      (HK.zeroLift Z).form.value ⟨_,((mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj)
        p.val).mp p.property).2⟩ := by
  have h := (mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj) p.val).mp p.property
  let u : X.domain := ⟨_,h.1⟩
  let v : rvLift Z.underlying.obj := ⟨_,h.2⟩
  have hp : p = (mixedPack X.domain (rvLift Z.underlying.obj)).toImage ⟨(u.val,v.val),u.property,v.property⟩ := by
    apply Subtype.ext
    change p.val = (Fin.append (m := n+1) (n := 0) (p.val.1 ∘ Fin.castAdd 0)
        (p.val.1 ∘ (Fin.natAdd (n+1) : Fin 0 → Fin ((n+1)+0))),
      Fin.append (p.val.2 ∘ Fin.castAdd Z.underlying.obj.arity) (p.val.2 ∘ Fin.natAdd X.arity))
    refine Prod.ext ?_ ?_
    · exact (Fin.append_castAdd_natAdd (m := n+1) (n := 0) (f := p.val.1)).symm
    · exact Fin.append_castAdd_natAdd.symm
  exact (congrArg (HK.positiveVFZeroProduct X Z).form.value hp).trans (HK.positiveVFZeroProduct_density_pair X Z u v)

set_option maxHeartbeats 1600000 in
theorem gamma_weighted_vf_zero_form_graph (hc : CanonicalStructure.IsCanonical (M := M))
    (hX : VFVolumeObjectGamma X G) (hZ : Z.Gamma G) :
    GammaGraphDefinable G (volumeFormGraph (HK.positiveVFZeroProduct X Z).form) := by
  have L := gammaLogicInput G
  have hZL := HK.zeroLift_gamma hZ
  have hXf := volume_form_graph_of_density_graph X.form hX.densityGraph
  have hRX := hXf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd 0 : Fin (n+1) → Fin ((n+1)+0))
      (Fin.castAdd Z.underlying.obj.arity : Fin X.arity → Fin (X.arity+Z.underlying.obj.arity)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hRZ := hZL.density.preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd (n+1) : Fin 0 → Fin ((n+1)+0))
      (Fin.natAdd X.arity : Fin Z.underlying.obj.arity → Fin (X.arity+Z.underlying.obj.arity)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hP₀ := L.comp_graph hRX (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hRZ (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hW := L.comp_graph (hP₀.inter hP₁) (gamma_rv_pair_multiply_graph hc G)
  have hR := L.restrict_graph (gamma_mixed_product_domain hX.domain hZL.set) hW
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro q y
  constructor
  · rintro ⟨hq,w,⟨⟨y₀,⟨u,hu,hy₀⟩,hw₀⟩,⟨y₁,⟨v,hv,hy₁⟩,hw₁⟩⟩,t,ht,hty⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change (HK.positiveVFZeroProduct X Z).form.value ⟨q,hq⟩ = (rvPairMultiply G.real t).val 0
    rw [weighted_vf_zero_density_point]
    have hu' : u = ⟨_,((mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj) q).mp hq).1⟩ :=
      Subtype.ext hu
    have hv' : v = ⟨_,((mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj) q).mp hq).2⟩ :=
      Subtype.ext hv
    subst hu' hv'
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    have hw0 : w.2 0 = (X.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = ((HK.zeroLift Z).form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans (congrFun hy₁ 0).symm
    change _ = w.2 0 * w.2 1
    rw [hw0,hw1]
    rfl
  · rintro ⟨⟨q',hq⟩,rfl,hy⟩
    have h := (mem_mixedProductDomain (n := n+1) (m := 0) X.domain (rvLift Z.underlying.obj) q').mp hq
    let w : Point (M := M) 0 2 :=
      (Fin.elim0,![(X.form.map ⟨_,h.1⟩).val 0,((HK.zeroLift Z).form.map ⟨_,h.2⟩).val 0])
    refine ⟨hq,w,⟨⟨(Fin.elim0,(X.form.map _).val),⟨⟨_,h.1⟩,rfl,rfl⟩,?_⟩,
      ⟨(Fin.elim0,((HK.zeroLift Z).form.map _).val),⟨⟨_,h.2⟩,rfl,rfl⟩,?_⟩⟩,
      ⟨w.2,Set.mem_univ _⟩,rfl,?_⟩
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rw [← hy]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change w.2 0 * w.2 1 = (HK.positiveVFZeroProduct X Z).form.value ⟨q',hq⟩
      rw [weighted_vf_zero_density_point]
      rfl

/-- **Weighted degree-zero factors of Gamma VF volume objects are Gamma.** -/
theorem VFVolumeObjectGamma.weightedZero (hc : CanonicalStructure.IsCanonical (M := M))
    (hX : VFVolumeObjectGamma X G) (hZ : Z.Gamma G) : VFVolumeObjectGamma (HK.positiveVFZeroProduct X Z) G :=
  ⟨gamma_mixed_product_domain hX.domain (HK.zeroLift_gamma hZ).set,
    density_graph_of_volume_form_graph _ (gamma_weighted_vf_zero_form_graph hc hX hZ)⟩

end WeightedZero

/-- The lift of a weighted positive-zero product is Gamma isomorphic to the weighted product of the lift. -/
theorem weighted_lift_zero_product_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) {k : ℕ} {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    (VFVolumeIso.of_bijection (HK.weightedLiftZeroProductBijection hc C U Z)).GammaDefinable G := by
  have hs := (rv_volume_lift_gamma hc C hGC hU).weightedZero hc hZ
  have ht := gamma_rv_lift_carrier hc C hGC (HK.positiveZeroProduct U Z) (hU.posZeroProd hc hZ)
  exact ⟨hs.domain,ht,vf_identity_map_gamma _ (fun _ => rfl) hs.domain⟩

open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry in
set_option maxHeartbeats 1600000 in
/-- Weighted degree-zero products of Gamma VF isomorphisms (identity on the factor) are Gamma. -/
theorem weighted_vf_zero_product_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k} {f : VFVolumeIso U V} (hf : f.GammaDefinable G)
    {Z : HK.ZeroRVVolumeObject (M := M) (C.base : Set M)} (hZ : Z.Gamma G) :
    (HK.weightedVFZeroProductIso hc C f (HK.ZeroRVVolumeIso.refl Z)).GammaDefinable G := by
  have hZL := HK.zeroLift_gamma hZ
  have hP := gamma_mixed_product_domain hf.source hZL.set
  have hQ := gamma_mixed_product_domain hf.target hZL.set
  refine ⟨hP,hQ,?_⟩
  have h₁ := (show VFBijGamma (HK.weightedVFZeroRestrictionBijection hc C U Z f.source f.source_subset) G from
    vf_identity_map_gamma _ (fun _ => rfl) hP).symm hc C
  have hg : GammaGraphDefinable G (vfMixedMapGraph
      (ordinaryFiniteAmbientIso (HK.zeroLiftIso (HK.ZeroRVVolumeIso.refl Z)).iso).hom) :=
    vf_identity_map_gamma _ (fun p => congrArg Subtype.val
      (SpecialTransformations.DefinableGeometry.Map.inverse_apply (liftLabelMap Z.underlying.obj)
        (zero_lift_label_map_bijective Z.underlying.obj) p)) hZL.set
  have h₂ : VFBijGamma (HK.weightedVFZeroProductBijection f.bijection
      (ordinaryFiniteAmbientIso (HK.zeroLiftIso (HK.ZeroRVVolumeIso.refl Z)).iso).hom
      (DefinableSetCat.bijective_of_iso (ordinaryFiniteAmbientIso (HK.zeroLiftIso (HK.ZeroRVVolumeIso.refl Z)).iso))
      (HK.zeroLiftIso (HK.ZeroRVVolumeIso.refl Z)).density) G :=
    gamma_mixed_domain_product_map_graph hf.graph hg hf.source hZL.set
  have h₃ : VFBijGamma (HK.weightedVFZeroRestrictionBijection hc C V Z f.target f.target_subset) G :=
    vf_identity_map_gamma _ (fun _ => rfl) hQ
  exact h₁.trans hc C (h₂.trans hc C h₃)

theorem CommonContextVolumeEquivalent.posZeroProd (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {k : ℕ} {U V : GammaVolumeObjects G (C.base : Set M) k} (h : CommonContextVolumeEquivalent G C U V)
    (Z : HK.GammaZeroRVObjects G (C.base : Set M)) :
    CommonContextVolumeEquivalent G C (U.posZeroProd hc Z) (V.posZeroProd hc Z) := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,h.weightedPositiveZero hc D ⟨Z.val.extend hCD,Z.property.extend hCD⟩⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

set_option maxHeartbeats 3200000 in
/-- **Contraction of weighted degree-zero factors.** -/
theorem gamma_weighted_zero_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (X : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hX : VFVolumeObjectGamma X G)
    (Z : HK.GammaZeroRVObjects G (C.base : Set M))
    (hXZ : VFVolumeObjectGamma (HK.positiveVFZeroProduct X Z.val) G)
    {σ υ : Equiv.Perm (Fin (k+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc X.densityGraph.domain) σ)
    (E' : StandardContraction (nativeMixedVolumeDomain hc (HK.positiveVFZeroProduct X Z.val).densityGraph.domain) υ)
    (hE : GammaProgramDefinable G E.program) (hE' : GammaProgramDefinable G E'.program) :
    CommonContextVolumeEquivalent G C
      ⟨(HK.positiveVFZeroProduct X Z.val).standardContractionObject hc C G.gamma E',
        standard_contraction_object_gamma hc C G hGC _ hXZ E' hE'⟩
      (GammaVolumeObjects.posZeroProd hc ⟨X.standardContractionObject hc C G.gamma E,
        standard_contraction_object_gamma hc C G hGC _ hX E hE⟩ Z) := by
  obtain ⟨P,⟨e,he⟩,hP⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    X hX E hE
  obtain ⟨Q,⟨e',he'⟩,hQ⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (HK.positiveVFZeroProduct X Z.val) hXZ E' hE'
  let f : VFVolumeIso (rvVolumeLift Q.val) (rvVolumeLift (P.posZeroProd hc Z).val) :=
    (e'.symm hc C).trans hc C ((HK.weightedVFZeroProductIso hc C e (HK.ZeroRVVolumeIso.refl Z.val)).trans hc C
      (VFVolumeIso.of_bijection (HK.weightedLiftZeroProductBijection hc C P.val Z.val)))
  have hf : f.GammaDefinable G :=
    (he'.symm hc C).trans hc C ((weighted_vf_zero_product_iso_gamma hc C he Z.property).trans hc C
      (weighted_lift_zero_product_iso_gamma hc C hGC P.property Z.property))
  have hK := rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 Q
    (P.posZeroProd hc Z) f hf
  exact ((hQ.symm hc).trans hc hK).trans hc (CommonContextVolumeEquivalent.posZeroProd hc hP Z)

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7

end IntegrationInACVF.Section7
