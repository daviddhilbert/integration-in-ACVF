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

end IntegrationInACVF.Section7.GammaFun
