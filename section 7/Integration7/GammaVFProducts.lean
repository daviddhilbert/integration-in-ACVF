import Integration7.GammaFunPositiveCoefficients
import Integration7.VolumeLiftProductBijections
import Integration7.GammaNamedPositiveClassification
import Integration7.GammaNamedBlowupProducts
import Integration7.VFVolumeProductIsomorphisms
import Integration7.GammaGenIntegralAdditivity

/-! Gamma certificates for Cartesian products of positive VF volume objects, and the Gamma lift
of products: the product of the lifts of two Gamma RV volume objects is Gamma isomorphic to the
lift of their product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n m : ℕ}

theorem gamma_mixed_product_domain {r s : ℕ}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n r) S}
    {B : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) m s) S}
    (hA : GammaSetDefinable G A.carrier) (hB : GammaSetDefinable G B.carrier) :
    GammaSetDefinable G (SpecialTransformations.Section4.mixedProductDomain A B).carrier := by
  have L := gammaLogicInput G
  have h1 := gamma_mixed_coordinate_preimage hA (Fin.castAdd m : Fin n → Fin (n+m)) (Fin.castAdd s : Fin r → Fin (r+s))
  have h2 := gamma_mixed_coordinate_preimage hB (Fin.natAdd n : Fin m → Fin (n+m)) (Fin.natAdd r : Fin s → Fin (r+s))
  convert L.inter h1 h2 using 1
  ext p
  exact SpecialTransformations.Section4.mem_mixedProductDomain A B p

theorem vf_product_density_point (U : PositiveVFVolumeObject (M := M) S n) (V : PositiveVFVolumeObject (M := M) S m)
    (p : (U.prod V).domain) :
    (U.prod V).form.value p =
      U.form.value ⟨_,((SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1) U.domain V.domain p.val).mp p.property).1⟩ *
        V.form.value ⟨_,((SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1) U.domain V.domain p.val).mp p.property).2⟩ := by
  have h := (SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1) U.domain V.domain p.val).mp
    p.property
  let u : U.domain := ⟨_,h.1⟩
  let v : V.domain := ⟨_,h.2⟩
  have hp : p = (SpecialTransformations.Section4.mixedPack U.domain V.domain).toImage
      ⟨(u.val,v.val),u.property,v.property⟩ := by
    apply Subtype.ext
    change p.val = (Fin.append (m := n+1) (n := m+1) (p.val.1 ∘ Fin.castAdd (m+1))
        (p.val.1 ∘ (Fin.natAdd (n+1) : Fin (m+1) → Fin ((n+1)+(m+1)))),
      Fin.append (p.val.2 ∘ Fin.castAdd V.arity) (p.val.2 ∘ Fin.natAdd U.arity))
    refine Prod.ext ?_ ?_
    · exact (Fin.append_castAdd_natAdd (m := n+1) (n := m+1) (f := p.val.1)).symm
    · exact Fin.append_castAdd_natAdd.symm
  exact (congrArg (U.prod V).form.value hp).trans (positive_vf_volume_product_density U V u v)

set_option maxHeartbeats 1600000 in
theorem gamma_vf_product_form_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveVFVolumeObject (M := M) S n} {V : PositiveVFVolumeObject (M := M) S m}
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G) :
    GammaGraphDefinable G (volumeFormGraph (U.prod V).form) := by
  have L := gammaLogicInput G
  have hUf := volume_form_graph_of_density_graph U.form hU.densityGraph
  have hVf := volume_form_graph_of_density_graph V.form hV.densityGraph
  have hRU := hUf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd (m+1) : Fin (n+1) → Fin ((n+1)+(m+1)))
      (Fin.castAdd V.arity : Fin U.arity → Fin (U.arity+V.arity)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hRV := hVf.preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd (n+1) : Fin (m+1) → Fin ((n+1)+(m+1)))
      (Fin.natAdd U.arity : Fin V.arity → Fin (U.arity+V.arity)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hP₀ := L.comp_graph hRU (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hRV (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hW := L.comp_graph (hP₀.inter hP₁) (gamma_rv_pair_multiply_graph hc G)
  have hR := L.restrict_graph (gamma_mixed_product_domain hU.domain hV.domain) hW
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro q y
  constructor
  · rintro ⟨hq,w,⟨⟨y₀,⟨u,hu,hy₀⟩,hw₀⟩,⟨y₁,⟨v,hv,hy₁⟩,hw₁⟩⟩,t,ht,hty⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change (U.prod V).form.value ⟨q,hq⟩ = (rvPairMultiply G.real t).val 0
    rw [vf_product_density_point]
    have hu' : u = ⟨_,((SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1)
        U.domain V.domain q).mp hq).1⟩ := Subtype.ext hu
    have hv' : v = ⟨_,((SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1)
        U.domain V.domain q).mp hq).2⟩ := Subtype.ext hv
    subst hu' hv'
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    have hw0 : w.2 0 = (U.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = (V.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans (congrFun hy₁ 0).symm
    change _ = w.2 0 * w.2 1
    rw [hw0,hw1]
    rfl
  · rintro ⟨⟨q',hq⟩,rfl,hy⟩
    have h := (SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1)
        U.domain V.domain q').mp hq
    let w : Point (M := M) 0 2 :=
      (Fin.elim0,![(U.form.map ⟨_,h.1⟩).val 0,(V.form.map ⟨_,h.2⟩).val 0])
    refine ⟨hq,w,⟨⟨(Fin.elim0,(U.form.map _).val),⟨⟨_,h.1⟩,rfl,rfl⟩,?_⟩,
      ⟨(Fin.elim0,(V.form.map _).val),⟨⟨_,h.2⟩,rfl,rfl⟩,?_⟩⟩,
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
      change w.2 0 * w.2 1 = (U.prod V).form.value ⟨q',hq⟩
      rw [vf_product_density_point]
      rfl

/-- **Products of Gamma VF volume objects are Gamma.** -/
theorem VFVolumeObjectGamma.prod (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveVFVolumeObject (M := M) S n} {V : PositiveVFVolumeObject (M := M) S m}
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G) : VFVolumeObjectGamma (U.prod V) G :=
  ⟨gamma_mixed_product_domain hU.domain hV.domain,
    density_graph_of_volume_form_graph _ (gamma_vf_product_form_graph hc hU hV)⟩

/-- **Gamma lift of products.** The identity inclusion from the product of lifts to the lift of
the product is a Gamma VF volume isomorphism. -/
theorem volume_lift_product_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) n} {V : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (hU : VolumeObjectGamma U G) (hV : VolumeObjectGamma V G) :
    (volumeLiftProductIso hc C U V).GammaDefinable G := by
  have hs := (rv_volume_lift_gamma hc C hGC hU).prod hc (rv_volume_lift_gamma hc C hGC hV)
  have ht := gamma_rv_lift_carrier hc C hGC (U.prod V) (hU.prod hc hV)
  exact ⟨hs.domain, ht, vf_identity_map_gamma (volumeLiftProductBijection hc C U V).map (fun _ => rfl) hs.domain⟩

section ProductMaps
variable {S : Set M} {U U' : PositiveVFVolumeObject (M := M) S n} {V V' : PositiveVFVolumeObject (M := M) S m}

theorem positive_vf_volume_product_map_value (f : SpecialTransformations.DefinableGeometry.Map U.domain U'.domain)
    (g : SpecialTransformations.DefinableGeometry.Map V.domain V'.domain) (w : (U.prod V).domain)
    (u : U.domain) (v : V.domain)
    (hu : u.val = (w.val.1 ∘ Fin.castAdd (m+1),w.val.2 ∘ Fin.castAdd V.arity))
    (hv : v.val = (w.val.1 ∘ (Fin.natAdd (n+1) : Fin (m+1) → Fin ((n+1)+(m+1))),w.val.2 ∘ Fin.natAdd U.arity)) :
    (positiveVFVolumeProductMap f g w).val =
      (Fin.append (m := n+1) (n := m+1) (f u).val.1 (g v).val.1,Fin.append (f u).val.2 (g v).val.2) := by
  have hw : w = (SpecialTransformations.Section4.mixedPack U.domain V.domain).toImage
      ⟨(u.val,v.val),u.property,v.property⟩ := by
    apply Subtype.ext
    change w.val = (Fin.append (m := n+1) (n := m+1) u.val.1 v.val.1,Fin.append u.val.2 v.val.2)
    rw [hu,hv]
    refine Prod.ext ?_ ?_
    · exact (Fin.append_castAdd_natAdd (m := n+1) (n := m+1) (f := w.val.1)).symm
    · exact Fin.append_castAdd_natAdd.symm
  subst hw
  simp only [positiveVFVolumeProductMap,SpecialTransformations.DefinableGeometry.Map.comp_apply,
    SpecialTransformations.Section4.mixedUnpack_pack]
  rfl

theorem gamma_positive_vf_volume_product_map_graph
    {f : SpecialTransformations.DefinableGeometry.Map U.domain U'.domain}
    {g : SpecialTransformations.DefinableGeometry.Map V.domain V'.domain}
    (hf : GammaGraphDefinable G (vfMixedMapGraph f)) (hg : GammaGraphDefinable G (vfMixedMapGraph g))
    (hU : GammaSetDefinable G U.domain.carrier) (hV : GammaSetDefinable G V.domain.carrier) :
    GammaGraphDefinable G (vfMixedMapGraph (positiveVFVolumeProductMap f g)) := by
  have L := gammaLogicInput G
  have hF := hf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd (m+1) : Fin (n+1) → Fin ((n+1)+(m+1)))
      (Fin.castAdd V.arity : Fin U.arity → Fin (U.arity+V.arity)) G.real)
    (mixedCoordinatePointMap (Fin.castAdd (m+1) : Fin (n+1) → Fin ((n+1)+(m+1)))
      (Fin.castAdd V'.arity : Fin U'.arity → Fin (U'.arity+V'.arity)) G.real)
  have hG := hg.preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd (n+1) : Fin (m+1) → Fin ((n+1)+(m+1)))
      (Fin.natAdd U.arity : Fin V.arity → Fin (U.arity+V.arity)) G.real)
    (mixedCoordinatePointMap (Fin.natAdd (n+1) : Fin (m+1) → Fin ((n+1)+(m+1)))
      (Fin.natAdd U'.arity : Fin V'.arity → Fin (U'.arity+V'.arity)) G.real)
  have hR := L.restrict_graph (gamma_mixed_product_domain hU hV) (hF.inter hG)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    rw [positive_vf_volume_product_map_value f g ⟨p,hp⟩ u v hu hv,hfu,hgv]
    refine Prod.ext ?_ ?_
    · exact Fin.append_castAdd_natAdd (m := n+1) (n := m+1) (f := q.1)
    · exact Fin.append_castAdd_natAdd
  · rintro ⟨w,rfl,rfl⟩
    have h := (SpecialTransformations.Section4.mem_mixedProductDomain (n := n+1) (m := m+1)
      U.domain V.domain w.val).mp w.property
    have hval := positive_vf_volume_product_map_value f g w ⟨_,h.1⟩ ⟨_,h.2⟩ rfl rfl
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

end ProductMaps

/-- **Products of Gamma VF volume isomorphisms are Gamma.** -/
theorem VFVolumeIso.GammaDefinable.prod (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' : PositiveVFVolumeObject (M := M) (C.base : Set M) n}
    {V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) m}
    {f : VFVolumeIso U U'} {g : VFVolumeIso V V'} (hf : f.GammaDefinable G) (hg : g.GammaDefinable G) :
    (f.prod hc C g).GammaDefinable G := by
  have hP := gamma_mixed_product_domain hf.source hg.source
  have hQ := gamma_mixed_product_domain hf.target hg.target
  refine ⟨hP,hQ,?_⟩
  have h₁ := (show VFBijGamma (vfVolumeProductRestrictionBijection hc C U V f.source g.source
    f.source_subset g.source_subset) G from vf_identity_map_gamma _ (fun _ => rfl) hP).symm hc C
  have h₂ : VFBijGamma (f.bijection.prod hc g.bijection) G :=
    gamma_positive_vf_volume_product_map_graph hf.graph hg.graph hf.source hg.source
  have h₃ : VFBijGamma (vfVolumeProductRestrictionBijection hc C U' V' f.target g.target
    f.target_subset g.target_subset) G := vf_identity_map_gamma _ (fun _ => rfl) hQ
  exact h₁.trans hc C (h₂.trans hc C h₃)

/-- Common-context equivalence respects positive products. -/
theorem CommonContextVolumeEquivalent.prod (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {k l : ℕ} {U U' : GammaVolumeObjects G (C.base : Set M) k} {V V' : GammaVolumeObjects G (C.base : Set M) l}
    (h : CommonContextVolumeEquivalent G C U U') (g : CommonContextVolumeEquivalent G C V V') :
    CommonContextVolumeEquivalent G C (U.prod hc V) (U'.prod hc V') := by
  obtain ⟨D,hCD,h⟩ := h
  obtain ⟨E,hCE,g⟩ := g
  obtain ⟨F,hDF,hEF⟩ := volume_context_join_exists D E
  have h1 := (h.extend hDF).product_right hc F (V.extend (hCD.trans hDF))
  have h2 := (g.extend hEF).product_left hc F (U'.extend (hCD.trans hDF))
  exact ⟨F,hCD.trans hDF,h1.trans hc F G h2⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k l : ℕ}

set_option maxHeartbeats 3200000 in
/-- **Contraction of products.** A Gamma standard contraction of a product of Gamma VF volume
objects is common-context equivalent to the product of contractions of the factors. -/
theorem gamma_prod_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField G.real) x → AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (W₁ : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (W₂ : PositiveVFVolumeObject (M := M) (C.base : Set M) l)
    (h₁ : VFVolumeObjectGamma W₁ G) (h₂ : VFVolumeObjectGamma W₂ G) (h₁₂ : VFVolumeObjectGamma (W₁.prod W₂) G)
    {σ₁ : Equiv.Perm (Fin (k+1))} {σ₂ : Equiv.Perm (Fin (l+1))} {σ : Equiv.Perm (Fin (((k+1)+l)+1))}
    (E₁ : StandardContraction (nativeMixedVolumeDomain hc W₁.densityGraph.domain) σ₁)
    (E₂ : StandardContraction (nativeMixedVolumeDomain hc W₂.densityGraph.domain) σ₂)
    (E : StandardContraction (nativeMixedVolumeDomain hc (W₁.prod W₂).densityGraph.domain) σ)
    (hE₁ : GammaProgramDefinable G E₁.program) (hE₂ : GammaProgramDefinable G E₂.program)
    (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      ⟨(W₁.prod W₂).standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC _ h₁₂ E hE⟩
      (GammaVolumeObjects.prod hc
        ⟨W₁.standardContractionObject hc C G.gamma E₁,standard_contraction_object_gamma hc C G hGC _ h₁ E₁ hE₁⟩
        ⟨W₂.standardContractionObject hc C G.gamma E₂,standard_contraction_object_gamma hc C G hGC _ h₂ E₂ hE₂⟩) := by
  obtain ⟨P₁,⟨e₁,he₁⟩,hP₁⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    W₁ h₁ E₁ hE₁
  obtain ⟨P₂,⟨e₂,he₂⟩,hP₂⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    W₂ h₂ E₂ hE₂
  obtain ⟨P,⟨e,he⟩,hP⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (W₁.prod W₂) h₁₂ E hE
  have hL := volume_lift_product_iso_gamma hc C hGC P₁.property P₂.property
  let f : VFVolumeIso (rvVolumeLift P.val) (rvVolumeLift (P₁.prod hc P₂).val) :=
    ((e.symm hc C).trans hc C ((e₁.prod hc C e₂).trans hc C (volumeLiftProductIso hc C P₁.val P₂.val)))
  have hf : f.GammaDefinable G :=
    (he.symm hc C).trans hc C ((he₁.prod hc C he₂).trans hc C hL)
  have hK := rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 P
    (P₁.prod hc P₂) f hf
  exact ((hP.symm hc).trans hc hK).trans hc (CommonContextVolumeEquivalent.prod hc hP₁ hP₂)

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7
end IntegrationInACVF.Section7
