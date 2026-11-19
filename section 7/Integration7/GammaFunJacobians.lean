import Integration7.GammaFunHeadFubini
import Integration7.SelectedFamilyJacobianIntegrals
import Integration7.VolumeFamilyRealizationIdentifications
import Integration7.GammaNamedJacobianTransport
import Integration7.GammaNamedDensityGraphs

/-! Gamma-named Jacobian transforms. Gamma-isomorphic full VF lifts of two Gamma-named
presentations have equal Gamma-named integrals; the Gamma Jacobian pushforward of a
presentation along a Gamma VF bijection uses a Gamma Jacobian value map, and preserves the
Gamma-named integral (change of variables on presentations). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b k : ℕ}

/-- The full VF lift of a Gamma family is a Gamma VF volume object. -/
theorem SelectedVFVolumeFamily.Gamma.fullLift (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) : VFVolumeObjectGamma F.fullLift G := by
  refine ⟨?_,?_⟩
  · exact gamma_native_selected_rv_vf_tail_lift hc (nativeMixedVolumeDomain hc F.domain) F.selected
      (by rw [nativeMixedVolumeDomain_carrier]; exact hF.domain)
  · change GammaSetDefinable G F.fullLift.densityGraph.domain.carrier
    rw [selected_family_full_lift_density_graph_carrier]
    exact gamma_native_selected_rv_vf_tail_lift hc (nativeMixedVolumeDomain hc F.densityGraph.domain)
      F.densityGraph.selected (by rw [nativeMixedVolumeDomain_carrier]; exact hF.densityGraph)

/-- The full VF lift of a Gamma family is Gamma isomorphic to the full lift of its density graph. -/
theorem gamma_full_lift_density_graph_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    ∃ e : VFVolumeIso F.fullLift F.densityGraph.fullLift, e.GammaDefinable G := by
  have hU := hF.fullLift hc
  have L := gammaLogicInput G
  let U := F.fullLift
  have hTarget : GammaSetDefinable G F.densityGraph.fullLift.domain.carrier :=
    gamma_native_selected_rv_vf_tail_lift hc (nativeMixedVolumeDomain hc F.densityGraph.domain)
      F.densityGraph.selected (by rw [nativeMixedVolumeDomain_carrier]; exact hF.densityGraph)
  have hAppend : GammaGraphDefinable G (vfMixedMapGraph (volumeDensityGraphBijection hc C U).map) := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.swap_graph hU.projection_graph)
    intro p q
    constructor
    · rintro ⟨hq,rfl⟩
      obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form q).mp hq
      exact ⟨⟨_,hq0⟩,rfl,hqe.symm⟩
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨((appendDensityMap U.form).toImage u).property,?_⟩
      change u.val = ((appendDensityMap U.form u).val.1,(appendDensityMap U.form u).val.2 ∘ Fin.castAdd 1)
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
  have he1 : (VFVolumeIso.of_bijection (volumeDensityGraphBijection hc C U)).GammaDefinable G :=
    ⟨hU.domain,hU.densityGraph,hAppend⟩
  have he2 : (VFVolumeIso.of_bijection (selectedFamilyFullLiftDensityGraphBijection hc F)).GammaDefinable G :=
    ⟨hU.densityGraph,hTarget,vf_identity_map_gamma _ (fun _ => rfl) hU.densityGraph⟩
  exact ⟨_,he1.trans hc C he2⟩

/-- Gamma isomorphisms transport along heterogeneous equalities of degree-cast objects. -/
theorem gamma_vf_iso_of_heq {S : Set M} {p q : ℕ} (h : p = q)
    {U U' : PositiveVFVolumeObject (M := M) S p} {V V' : PositiveVFVolumeObject (M := M) S q}
    (hU : HEq U V) (hU' : HEq U' V') (e : VFVolumeIso U U') (he : e.GammaDefinable G) :
    ∃ e' : VFVolumeIso V V', e'.GammaDefinable G := by
  subst h
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hU'
  exact ⟨e,he⟩

/-- Equality of labels is a Gamma relation. -/
theorem gamma_label_eq_graph {m : ℕ} :
    GammaGraphDefinable G (fun (p q : Point (M := M) m a) => q.2 = p.2) := by
  let L := gammaLogicInput G
  let Z := SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) 0 a) G.real
  have ht := (L.real_map_graph (SpecialTransformations.Section5.Map.id Z)).preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin m) (id : Fin a → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin m) (id : Fin a → Fin a) G.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ht
  intro p q
  constructor
  · rintro ⟨z,hz,hq⟩
    exact (congrArg Prod.snd (hz.symm.trans hq)).symm
  · intro he
    refine ⟨⟨(Fin.elim0,p.2),Set.mem_univ _⟩,?_,?_⟩
    · exact Prod.ext (by funext j; exact j.elim0) rfl
    · exact Prod.ext (by funext j; exact j.elim0) he.symm

/-- The pure VF graph of a map of VF sets, as a Gamma relation on points. -/
def PureVFMapGamma {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : SpecialTransformations.DefinableGeometry.Map X Y) (G : Base (M := M)) : Prop :=
  GammaGraphDefinable G (fun (x y : Point (M := M) n 0) => ∃ u : X, u.val = x.1 ∧ (φ u).val = y.1)

/-- The mixed base map of a Gamma VF map on a Gamma mixed set has a Gamma graph. -/
theorem gamma_mixed_vf_base_map_graph
    {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (φ : SpecialTransformations.DefinableGeometry.Map X Y) (hφ : PureVFMapGamma φ G)
    (U : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) (C.base : Set M))
    (hU : GammaSetDefinable G U.carrier) (hUX : ∀ p : U, p.val.1 ∈ X.carrier) :
    GammaGraphDefinable G (vfMixedMapGraph (mixedVFBaseMap φ U hUX).toImage) := by
  let L := gammaLogicInput G
  have hB := hφ.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.elim0 : Fin 0 → Fin a) G.real)
    (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.elim0 : Fin 0 → Fin a) G.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (L.restrict_graph hU (hB.inter (gamma_label_eq_graph (G := G) (m := n) (a := a))))
  intro p q
  constructor
  · rintro ⟨hp,⟨u,hu,hφu⟩,hl⟩
    let w : U := ⟨p,hp⟩
    have huw : u = ⟨w.val.1,hUX w⟩ := Subtype.ext hu
    refine ⟨w,rfl,?_⟩
    change ((φ ⟨w.val.1,hUX w⟩).val,w.val.2) = q
    rw [← huw]
    exact Prod.ext hφu hl.symm
  · rintro ⟨w,rfl,rfl⟩
    exact ⟨w.property,⟨⟨w.val.1,hUX w⟩,rfl,rfl⟩,rfl⟩

/-- The selected VF tail lift of a Gamma mixed map has a Gamma graph. -/
theorem gamma_selected_tail_lift_map_graph (hc : CanonicalStructure.IsCanonical (M := M)) {d : ℕ}
    {A B : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) (C.base : Set M)}
    (f : SpecialTransformations.DefinableGeometry.Map A B) (hLabels : ∀ p : A, (f p).val.2 = p.val.2)
    (ρ : Fin d → Fin a) (hA : GammaSetDefinable G A.carrier) (hf : GammaGraphDefinable G (vfMixedMapGraph f)) :
    GammaGraphDefinable G (vfMixedMapGraph (selectedTailLiftMap f hLabels ρ)) := by
  let L := gammaLogicInput G
  have hHead := hf.preimage_maps
    (mixedCoordinatePointMap (Fin.castAdd d) (id : Fin a → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.castAdd d) (id : Fin a → Fin a) G.real)
  let Z := SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) d 0) G.real
  have ht := (L.real_map_graph (SpecialTransformations.Section5.Map.id Z)).preimage_maps
    (mixedCoordinatePointMap (Fin.natAdd n) (Fin.elim0 : Fin 0 → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.natAdd n) (Fin.elim0 : Fin 0 → Fin a) G.real)
  have hTail : GammaGraphDefinable G (fun (p : Point (M := M) (n+d) a) (q : Point (M := M) (n+d) a) =>
      p.1 ∘ Fin.natAdd n = q.1 ∘ Fin.natAdd n) := by
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr ht
    intro p q
    constructor
    · rintro ⟨z,hz,hq⟩
      exact congrArg Prod.fst (hz.symm.trans hq)
    · intro he
      refine ⟨⟨(p.1 ∘ Fin.natAdd n,Fin.elim0),Set.mem_univ _⟩,?_,?_⟩
      · exact Prod.ext rfl (by funext j; exact j.elim0)
      · exact Prod.ext he (by funext j; exact j.elim0)
  have hLift : GammaSetDefinable G (selectedRVVFTailLift A ρ).carrier :=
    gamma_native_selected_rv_vf_tail_lift hc (nativeMixedVolumeDomain hc A) ρ
      (by rw [nativeMixedVolumeDomain_carrier]; exact hA)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hLift (hHead.inter hTail))
  intro p q
  constructor
  · rintro ⟨hp,⟨u,hu,hfu⟩,ht⟩
    let w : selectedRVVFTailLift A ρ := ⟨p,hp⟩
    refine ⟨w,rfl,?_⟩
    rw [selected_tail_lift_map_value]
    have hproj : selectedRVVFTailProjection A ρ w = u := Subtype.ext hu.symm
    rw [hproj,hfu]
    change (Fin.append (q.1 ∘ Fin.castAdd d) (p.1 ∘ Fin.natAdd n),p.2) = q
    have hl : q.2 = p.2 := by
      have h1 := congrArg Prod.snd hfu
      change (f u).val.2 = q.2 ∘ id at h1
      rw [hLabels u] at h1
      have h2 := congrArg Prod.snd hu
      change u.val.2 = p.2 ∘ id at h2
      exact h1.symm.trans h2
    rw [ht]
    exact Prod.ext Fin.append_castAdd_natAdd hl.symm
  · rintro ⟨w,rfl,rfl⟩
    refine ⟨w.property,⟨selectedRVVFTailProjection A ρ w,rfl,?_⟩,?_⟩
    · rw [selected_tail_lift_map_value]
      exact Prod.ext (funext (Fin.append_left _ _)).symm (hLabels _)
    · rw [selected_tail_lift_map_value]
      exact (funext (Fin.append_right _ _)).symm

/-- Jacobian pushforward of a family along a VF bijection, using a prescribed Jacobian value map. -/
def SelectedVFVolumeFamily.jacobianPushforwardWith
    {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : SpecialTransformations.DefinableGeometry.Map X Y)
    (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (j : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M))) : SelectedVFVolumeFamily C n a k where
  domain := (mixedVFBaseMap φ F.domain hF).image
  selected := F.selected
  finite_selected := (F.pushforwardBase φ hφ hF).finite_selected
  form := jacobianTransportedForm (mixedVFBaseMap φ F.domain hF).toImage
    (mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF) j F.form

/-- The Jacobian pushforward preserves VF volume along the base map. -/
theorem SelectedVFVolumeFamily.jacobianPushforwardWith_preserves (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hn : 0 < n)
    {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : SpecialTransformations.DefinableGeometry.Map X Y)
    (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (j : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (hj : IsJacobianValueMap (mixedVFBaseMap φ F.domain hF).toImage j) :
    PreservesVFVolume F.form (F.jacobianPushforwardWith φ hφ hF j).form (mixedVFBaseMap φ F.domain hF).toImage :=
  preserves_jacobian_transported_form hc C hn _ _ j hj F.form

/-- The full-lift volume bijection of a Jacobian pushforward. -/
def jacobianWithFullLiftBijection (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {X Y : SpecialTransformations.DefinableGeometry.DefSet
      (SpecialTransformations.Section4.rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : SpecialTransformations.DefinableGeometry.Map X Y)
    (hφ : Function.Bijective φ) (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (j : SpecialTransformations.DefinableGeometry.Map F.domain
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1)
        (C.base : Set M)))
    (hj : IsJacobianValueMap (mixedVFBaseMap φ F.domain hF).toImage j) :
    VFVolumeBijection F.fullLift (F.jacobianPushforwardWith φ hφ hF j).fullLift where
  map := selectedTailLiftMap (mixedVFBaseMap φ F.domain hF).toImage (fun _ => rfl) F.selected
  bijective := selected_tail_lift_map_bijective _ (mixed_vf_base_map_to_image_bijective φ hφ.1 F.domain hF)
    (fun _ => rfl) F.selected
  preserves := preserves_vf_volume_selected_tail hc C (Nat.zero_lt_succ k) _ (fun _ => rfl) F.form
    (F.jacobianPushforwardWith φ hφ hF j).form F.selected
    (F.jacobianPushforwardWith_preserves hc C hn φ hφ hF j hj)

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Integrals from full lifts.** Gamma-isomorphic full VF lifts give equal Gamma-named
integrals. -/
theorem presentation_integral_eq_of_full_lift_iso (F H : Presentation C Ξ hΞ n k)
    (e : VFVolumeIso F.family.fullLift H.family.fullLift) (he : e.GammaDefinable 𝔅) :
    F.integral hc C Ξ hΞ hGenerated = H.integral hc C Ξ hΞ hGenerated := by
  obtain ⟨eF,heF⟩ := gamma_full_lift_density_graph_iso hc 𝔇 F.gamma
  obtain ⟨eH,heH⟩ := gamma_full_lift_density_graph_iso hc 𝔇 H.gamma
  obtain ⟨f,hf⟩ := gamma_vf_iso_of_heq (family_realization_degree_eq n k)
    (family_density_graph_full_lift_realization_heq hc F.family)
    (family_density_graph_full_lift_realization_heq hc H.family)
    ((eF.symm hc 𝔇).trans hc 𝔇 (e.trans hc 𝔇 eH)) ((heF.symm hc 𝔇).trans hc 𝔇 (he.trans hc 𝔇 heH))
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  let A' := nativeMixedVolumeDomain hc H.family.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hA' : GammaSetDefinable 𝔅 (carrier A') := H.gamma.native_domain hc
  have hW := realization_gamma hc C Ξ hΞ A hA F.family.densityGraph.selected F.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero
  have hW' := realization_gamma hc C Ξ hΞ A' hA' H.family.densityGraph.selected
    H.family.densityGraph.finite_selected (Fin.last H.arity) H.family.densityGraph_label_nonzero
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  let W := selectedCoordinateVolumeRealization hc A F.family.densityGraph.selected
    F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let W' := selectedCoordinateVolumeRealization hc A' H.family.densityGraph.selected
    H.family.densityGraph.finite_selected (Fin.last H.arity) H.family.densityGraph_label_nonzero
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  obtain ⟨EW',hEW',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W'.densityGraph.domain) hW'.densityGraph (Equiv.refl _)
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  have h1 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hA F.family.densityGraph.selected F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero
    (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated) hW EW hEW
  have h2 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A' hA' H.family.densityGraph.selected H.family.densityGraph.finite_selected (Fin.last H.arity)
    H.family.densityGraph_label_nonzero
    (H.contraction hc C Ξ hΞ hGenerated) (H.contraction_gamma hc C Ξ hΞ hGenerated) hW' EW' hEW'
  have h3 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    _ _ hW hW' f hf EW EW' hEW hEW'
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    (((h1.trans hc h3).trans hc (h2.symm hc)).descend hc 𝔇 hNames)

/-- A Gamma VF bijection between Gamma VF sets in `VF^(n+1)`. -/
structure GammaVFBijection (X Y : GammaVFSet C Ξ hΞ n) where
  map : SpecialTransformations.DefinableGeometry.Map X.set Y.set
  bijective : Function.Bijective map
  gamma : PureVFMapGamma map (gammaNamedBase C Ξ)

/-- A presentation is supported in a Gamma VF set when its VF base lies in it. -/
def Presentation.SupportedIn (F : Presentation C Ξ hΞ n k) (X : GammaVFSet C Ξ hΞ n) : Prop :=
  ∀ p : F.family.domain, p.val.1 ∈ X.set.carrier

include hc in
theorem presentation_jacobian_value_exists {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    ∃ j : SpecialTransformations.DefinableGeometry.Map F.family.domain
        (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawVFSpace (M := M) 1) 𝔖),
      GammaGraphDefinable 𝔅 (fun (p : Point (M := M) (n+1) F.arity) (z : Point (M := M) 1 0) =>
        ∃ u : F.family.domain, u.val = p ∧ (j u).val = z.1) ∧
      IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage j :=
  gamma_exists_totalMixedJacobianMap hc (Nat.zero_lt_succ n) _
    (gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF)

/-- The chosen Gamma Jacobian value map of a supported presentation. -/
def Presentation.jacobianValue {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :=
  Classical.choose (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)

/-- **The Gamma Jacobian transform of a supported presentation** along a Gamma VF bijection. -/
def Presentation.jacobian {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) : Presentation C Ξ hΞ n k where
  arity := F.arity
  family := F.family.jacobianPushforwardWith φ.map φ.bijective hF (F.jacobianValue hc C Ξ hΞ φ hF)
  gamma := by
    have hspec := Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)
    have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
    refine ⟨?_,?_⟩
    · convert (gammaLogicInput 𝔅).image_graph hfΓ using 1
      ext q
      constructor
      · rintro ⟨u,hu⟩
        exact ⟨u.val,u,rfl,hu⟩
      · rintro ⟨_,u,rfl,hu⟩
        exact ⟨u,hu⟩
    · exact density_graph_of_volume_form_graph _
        (gamma_jacobian_transported_form_graph hc _ _ hfΓ _ hspec.1 F.family.form
          (volume_form_graph_of_density_graph F.family.form F.gamma.densityGraph))

theorem Presentation.jacobianValue_spec {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    IsJacobianValueMap (mixedVFBaseMap φ.map F.family.domain hF).toImage (F.jacobianValue hc C Ξ hΞ φ hF) :=
  (Classical.choose_spec (presentation_jacobian_value_exists hc C Ξ hΞ F φ hF)).2

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Gamma change of variables on presentations.** -/
theorem presentation_jacobian_integral {X Y : GammaVFSet C Ξ hΞ n} (F : Presentation C Ξ hΞ n k)
    (φ : GammaVFBijection C Ξ hΞ X Y) (hF : F.SupportedIn C Ξ hΞ X) :
    (F.jacobian hc C Ξ hΞ φ hF).integral hc C Ξ hΞ hGenerated = F.integral hc C Ξ hΞ hGenerated := by
  let b := jacobianWithFullLiftBijection hc 𝔇 (Nat.zero_lt_succ n) F.family φ.map φ.bijective hF
    (F.jacobianValue hc C Ξ hΞ φ hF) (F.jacobianValue_spec hc C Ξ hΞ φ hF)
  have hfΓ := gamma_mixed_vf_base_map_graph φ.map φ.gamma _ F.gamma.domain hF
  have hb : (VFVolumeIso.of_bijection b).GammaDefinable 𝔅 :=
    ⟨(F.gamma.fullLift hc).domain,((F.jacobian hc C Ξ hΞ φ hF).gamma.fullLift hc).domain,
      gamma_selected_tail_lift_map_graph hc _ (fun _ => rfl) F.family.selected F.gamma.domain hfΓ⟩
  exact (presentation_integral_eq_of_full_lift_iso hc C Ξ hΞ hGenerated γ hγ hγ1 F (F.jacobian hc C Ξ hΞ φ hF)
    (VFVolumeIso.of_bijection b) hb).symm

end IntegrationInACVF.Section7.GammaFun
