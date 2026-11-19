import Integration7.GammaGenIntegralAdditivity

/-! Additivity of the Gamma-named integral. The coproduct of Gamma VF volume objects is a
Gamma VF volume object, the full lift of a family sum is Gamma isomorphic to the coproduct of
the full lifts (forget the appended selected coordinates), and hence the Gamma-named integral of
the sum of two presentations is the sum of their integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.Section4 (rvLeftTag rvRightTag rawVFSpace rawRVSpace rawMixedSpace tupleRV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b k : ℕ}

/-- **Coproducts of Gamma VF volume objects are Gamma.** -/
theorem VFVolumeObjectGamma.coprod {S : Set M} {U V : PositiveVFVolumeObject (M := M) S k}
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G) : VFVolumeObjectGamma (U.coprod V) G := by
  have L := gammaLogicInput G
  refine ⟨vf_coprod_domain_gamma hU.domain hV.domain,density_graph_of_volume_form_graph _ ?_⟩
  have hfU := volume_form_graph_of_density_graph U.form hU.densityGraph
  have hfV := volume_form_graph_of_density_graph V.form hV.densityGraph
  have h := L.union_graph
    (L.comp_graph (L.swap_graph (L.restrict_graph hU.domain (gamma_vf_left_tag_relation (B := G) (b := V.arity)))) hfU)
    (L.comp_graph (L.swap_graph (L.restrict_graph hV.domain (gamma_vf_right_tag_relation (B := G) (a := U.arity)))) hfV)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro q y
  constructor
  · rintro (⟨p,⟨hp,rfl⟩,⟨u,rfl,hu⟩⟩ | ⟨p,⟨hp,rfl⟩,⟨u,rfl,hu⟩⟩)
    · refine ⟨vfVolumeCoprodLeftMap U V u,rfl,?_⟩
      rw [← hu]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact vf_volume_coprod_density_left U V u
    · refine ⟨vfVolumeCoprodRightMap U V u,rfl,?_⟩
      rw [← hu]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact vf_volume_coprod_density_right U V u
  · rintro ⟨w,rfl,hw⟩
    rcases vf_volume_coprod_cases U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · refine Or.inl ⟨u.val,⟨u.property,rfl⟩,⟨u,rfl,?_⟩⟩
      rw [← hw]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact (vf_volume_coprod_density_left U V u).symm
    · refine Or.inr ⟨v.val,⟨v.property,rfl⟩,⟨v,rfl,?_⟩⟩
      rw [← hw]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact (vf_volume_coprod_density_right U V v).symm

theorem sum_full_lift_cases (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (p : (selectedVolumeFamilySum F H).fullLift.domain) :
    (∃ u : F.fullLift.domain, p.val = (u.val.1,Fin.append (rvLeftTag b u.val.2) (u.val.2 ∘ F.selected))) ∨
      ∃ v : H.fullLift.domain, p.val = (v.val.1,Fin.append (rvRightTag a v.val.2) (v.val.2 ∘ H.selected)) := by
  obtain ⟨h1,h2⟩ := (mem_selected_rv_vf_tail_lift (selectedVolumeFamilySum F H).domain
    (selectedVolumeFamilySum F H).selected p.val).mp p.property
  change tupleRV (p.val.1 ∘ Fin.natAdd n) = p.val.2 ∘ Fin.natAdd (1+(a+b)) at h2
  rcases (mem_selected_volume_family_sum F H _).mp h1 with ⟨u,hu⟩ | ⟨v,hv⟩
  · have hx : u.val.1 = p.val.1 ∘ Fin.castAdd (k+1) := congrArg Prod.fst hu
    have hr : Fin.append (rvLeftTag b u.val.2) (u.val.2 ∘ F.selected) = p.val.2 := congrArg Prod.snd hu
    have hm : (p.val.1,u.val.2) ∈ F.fullLift.domain.carrier := by
      refine (mem_selected_rv_vf_tail_lift _ _ _).mpr ⟨?_,?_⟩
      · change (p.val.1 ∘ Fin.castAdd (k+1),u.val.2) ∈ F.domain.carrier
        rw [← hx]
        exact u.property
      · change tupleRV (p.val.1 ∘ Fin.natAdd n) = u.val.2 ∘ F.selected
        rw [h2,← hr]
        funext j
        exact Fin.append_right _ _ j
    exact Or.inl ⟨⟨_,hm⟩,Prod.ext rfl hr.symm⟩
  · have hx : v.val.1 = p.val.1 ∘ Fin.castAdd (k+1) := congrArg Prod.fst hv
    have hr : Fin.append (rvRightTag a v.val.2) (v.val.2 ∘ H.selected) = p.val.2 := congrArg Prod.snd hv
    have hm : (p.val.1,v.val.2) ∈ H.fullLift.domain.carrier := by
      refine (mem_selected_rv_vf_tail_lift _ _ _).mpr ⟨?_,?_⟩
      · change (p.val.1 ∘ Fin.castAdd (k+1),v.val.2) ∈ H.domain.carrier
        rw [← hx]
        exact v.property
      · change tupleRV (p.val.1 ∘ Fin.natAdd n) = v.val.2 ∘ H.selected
        rw [h2,← hr]
        funext j
        exact Fin.append_right _ _ j
    exact Or.inr ⟨⟨_,hm⟩,Prod.ext rfl hr.symm⟩

/-- The map from the full lift of a family sum to the coproduct of the full lifts. -/
def sumFullLiftCoprodMap (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k) :
    Map (selectedVolumeFamilySum F H).fullLift.domain (F.fullLift.coprod H.fullLift).domain :=
  (((Map.fst (rawVFSpace (n+(k+1))) (rawRVSpace ((1+(a+b))+(k+1))) (C.base : Set M) _).pair
    ((rvCoordinateSelectMap (C.base : Set M) (Fin.castAdd (k+1))).comp
      (Map.snd (rawVFSpace (n+(k+1))) (rawRVSpace ((1+(a+b))+(k+1))) (C.base : Set M) _))).toUniv).corestrict (by
    intro p
    rcases sum_full_lift_cases F H p with ⟨u,hu⟩ | ⟨v,hv⟩
    · refine Or.inl ⟨u,?_⟩
      change (u.val.1,rvLeftTag b u.val.2) = (p.val.1,p.val.2 ∘ Fin.castAdd (k+1))
      rw [hu]
      refine Prod.ext rfl ?_
      funext j
      exact (Fin.append_left _ _ j).symm
    · refine Or.inr ⟨v,?_⟩
      change (v.val.1,rvRightTag a v.val.2) = (p.val.1,p.val.2 ∘ Fin.castAdd (k+1))
      rw [hv]
      refine Prod.ext rfl ?_
      funext j
      exact (Fin.append_left _ _ j).symm)

theorem sum_full_lift_coprod_map_value (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (p : (selectedVolumeFamilySum F H).fullLift.domain) :
    (sumFullLiftCoprodMap F H p).val = (p.val.1,p.val.2 ∘ Fin.castAdd (k+1)) := rfl

theorem sum_full_lift_coprod_map_left (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (p : (selectedVolumeFamilySum F H).fullLift.domain) (u : F.fullLift.domain)
    (hu : p.val = (u.val.1,Fin.append (rvLeftTag b u.val.2) (u.val.2 ∘ F.selected))) :
    sumFullLiftCoprodMap F H p = vfVolumeCoprodLeftMap F.fullLift H.fullLift u := by
  apply Subtype.ext
  rw [sum_full_lift_coprod_map_value,hu]
  refine Prod.ext rfl ?_
  funext j
  exact Fin.append_left _ _ j

theorem sum_full_lift_coprod_map_right (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (p : (selectedVolumeFamilySum F H).fullLift.domain) (v : H.fullLift.domain)
    (hv : p.val = (v.val.1,Fin.append (rvRightTag a v.val.2) (v.val.2 ∘ H.selected))) :
    sumFullLiftCoprodMap F H p = vfVolumeCoprodRightMap F.fullLift H.fullLift v := by
  apply Subtype.ext
  rw [sum_full_lift_coprod_map_value,hv]
  refine Prod.ext rfl ?_
  funext j
  exact Fin.append_left _ _ j

theorem sum_full_lift_coprod_map_bijective (F : SelectedVFVolumeFamily C n a k)
    (H : SelectedVFVolumeFamily C n b k) : Function.Bijective (sumFullLiftCoprodMap F H) := by
  constructor
  · intro p p' hpp
    have he : (p.val.1,p.val.2 ∘ Fin.castAdd (k+1)) = (p'.val.1,p'.val.2 ∘ Fin.castAdd (k+1)) :=
      congrArg (fun w : (F.fullLift.coprod H.fullLift).domain => w.val) hpp
    obtain ⟨h1,h2⟩ := Prod.mk.inj he
    apply Subtype.ext
    rcases sum_full_lift_cases F H p with ⟨r,hr⟩ | ⟨r,hr⟩ <;>
      rcases sum_full_lift_cases F H p' with ⟨r',hr'⟩ | ⟨r',hr'⟩
    · have ht : rvLeftTag b r.val.2 = rvLeftTag b r'.val.2 := by
        have := h2
        rw [hr,hr'] at this
        funext j
        simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
      have hrr := SpecialTransformations.Section4.rvLeftTag_injective b ht
      refine Prod.ext h1 ?_
      rw [hr,hr']
      simp only [hrr]
    · exfalso
      have := h2
      rw [hr,hr'] at this
      apply SpecialTransformations.Section4.rvTag_disjoint (n := a) (m := b) r.val.2 r'.val.2
      funext j
      simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
    · exfalso
      have := h2
      rw [hr,hr'] at this
      apply SpecialTransformations.Section4.rvTag_disjoint (n := a) (m := b) r'.val.2 r.val.2
      funext j
      simpa only [Function.comp_apply,Fin.append_left] using (congrFun this j).symm
    · have ht : rvRightTag a r.val.2 = rvRightTag a r'.val.2 := by
        have := h2
        rw [hr,hr'] at this
        funext j
        simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
      have hrr := SpecialTransformations.Section4.rvRightTag_injective a ht
      refine Prod.ext h1 ?_
      rw [hr,hr']
      simp only [hrr]
  · intro t
    rcases vf_volume_coprod_cases F.fullLift H.fullLift t with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · obtain ⟨hu1,hu2⟩ := (mem_selected_rv_vf_tail_lift F.domain F.selected u.val).mp u.property
      have hm : (u.val.1,Fin.append (rvLeftTag b u.val.2) (u.val.2 ∘ F.selected)) ∈
          (selectedVolumeFamilySum F H).fullLift.domain.carrier := by
        refine (mem_selected_rv_vf_tail_lift _ _ _).mpr ⟨?_,?_⟩
        · exact (mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨⟨_,hu1⟩,rfl⟩)
        · change tupleRV (u.val.1 ∘ Fin.natAdd n) =
            Fin.append (rvLeftTag b u.val.2) (u.val.2 ∘ F.selected) ∘ Fin.natAdd (1+(a+b))
          rw [hu2]
          funext j
          exact (Fin.append_right _ _ j).symm
      exact ⟨⟨_,hm⟩,sum_full_lift_coprod_map_left F H _ u rfl⟩
    · obtain ⟨hv1,hv2⟩ := (mem_selected_rv_vf_tail_lift H.domain H.selected v.val).mp v.property
      have hm : (v.val.1,Fin.append (rvRightTag a v.val.2) (v.val.2 ∘ H.selected)) ∈
          (selectedVolumeFamilySum F H).fullLift.domain.carrier := by
        refine (mem_selected_rv_vf_tail_lift _ _ _).mpr ⟨?_,?_⟩
        · exact (mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨⟨_,hv1⟩,rfl⟩)
        · change tupleRV (v.val.1 ∘ Fin.natAdd n) =
            Fin.append (rvRightTag a v.val.2) (v.val.2 ∘ H.selected) ∘ Fin.natAdd (1+(a+b))
          rw [hv2]
          funext j
          exact (Fin.append_right _ _ j).symm
      exact ⟨⟨_,hm⟩,sum_full_lift_coprod_map_right F H _ v rfl⟩

theorem sum_full_lift_coprod_density (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (p : (selectedVolumeFamilySum F H).fullLift.domain) :
    (selectedVolumeFamilySum F H).fullLift.form.value p =
      (F.fullLift.coprod H.fullLift).form.value (sumFullLiftCoprodMap F H p) := by
  rcases sum_full_lift_cases F H p with ⟨u,hu⟩ | ⟨v,hv⟩
  · rw [sum_full_lift_coprod_map_left F H p u hu,vf_volume_coprod_density_left]
    let u' : F.domain := ⟨(u.val.1 ∘ Fin.castAdd (k+1),u.val.2),
      ((mem_selected_rv_vf_tail_lift F.domain F.selected u.val).mp u.property).1⟩
    have hmem := (mem_selected_volume_family_sum F H (sumLeftPoint F b u'.val)).mpr (Or.inl ⟨u',rfl⟩)
    have hs : selectedRVVFTailProjection (selectedVolumeFamilySum F H).domain
        (selectedVolumeFamilySum F H).selected p = ⟨_,hmem⟩ := by
      apply Subtype.ext
      change (p.val.1 ∘ Fin.castAdd (k+1),p.val.2) = sumLeftPoint F b u'.val
      rw [hu]
      rfl
    change (selectedVolumeFamilySum F H).form.value (selectedRVVFTailProjection _ _ p) =
      F.form.value (selectedRVVFTailProjection _ _ u)
    rw [hs,selected_volume_family_sum_density_left]
    rfl
  · rw [sum_full_lift_coprod_map_right F H p v hv,vf_volume_coprod_density_right]
    let v' : H.domain := ⟨(v.val.1 ∘ Fin.castAdd (k+1),v.val.2),
      ((mem_selected_rv_vf_tail_lift H.domain H.selected v.val).mp v.property).1⟩
    have hmem := (mem_selected_volume_family_sum F H (sumRightPoint H a v'.val)).mpr (Or.inr ⟨v',rfl⟩)
    have hs : selectedRVVFTailProjection (selectedVolumeFamilySum F H).domain
        (selectedVolumeFamilySum F H).selected p = ⟨_,hmem⟩ := by
      apply Subtype.ext
      change (p.val.1 ∘ Fin.castAdd (k+1),p.val.2) = sumRightPoint H a v'.val
      rw [hv]
      rfl
    change (selectedVolumeFamilySum F H).form.value (selectedRVVFTailProjection _ _ p) =
      H.form.value (selectedRVVFTailProjection _ _ v)
    rw [hs,selected_volume_family_sum_density_right]
    rfl

/-- The full lift of a family sum is isomorphic to the coproduct of the full lifts. -/
def sumFullLiftCoprodIso (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (H : SelectedVFVolumeFamily C n b k) :
    VFVolumeIso (selectedVolumeFamilySum F H).fullLift (F.fullLift.coprod H.fullLift) :=
  VFVolumeIso.of_bijection (VFVolumeBijection.of_preserving_vf_and_density hc C (sumFullLiftCoprodMap F H)
    (sum_full_lift_coprod_map_bijective F H) (fun _ => rfl) (sum_full_lift_coprod_density F H))

/-- **The full-lift sum isomorphism is Gamma.** -/
theorem sum_full_lift_coprod_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} {H : SelectedVFVolumeFamily C n b k} (hF : F.Gamma G) (hH : H.Gamma G) :
    (sumFullLiftCoprodIso hc F H).GammaDefinable G := by
  have L := gammaLogicInput G
  have hS := ((hF.sum hH).fullLift hc).domain
  have hT := vf_coprod_domain_gamma (hF.fullLift hc).domain (hH.fullLift hc).domain
  refine ⟨hS,hT,?_⟩
  have hg := gamma_global_map_graph (B := G)
    (mixedCoordinatePointMap (id : Fin (n+(k+1)) → Fin (n+(k+1))) (Fin.castAdd (k+1) : Fin (1+(a+b)) → _) G.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hS hg)
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u.property,rfl⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

theorem vf_coprod_heq {S : Set M} {p q : ℕ} (h : p = q) {U U' : PositiveVFVolumeObject (M := M) S p}
    {V V' : PositiveVFVolumeObject (M := M) S q} (hU : HEq U V) (hU' : HEq U' V') :
    HEq (U.coprod U') (V.coprod V') := by
  subst h
  obtain rfl := eq_of_heq hU
  obtain rfl := eq_of_heq hU'
  rfl

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 3200000 in
include hγ hγ1 in
/-- **Additivity of the Gamma-named integral.** -/
theorem presentation_integral_add (F H : Presentation C Ξ hΞ n k) :
    (F.add C Ξ hΞ H).integral hc C Ξ hΞ hGenerated =
      F.integral hc C Ξ hΞ hGenerated + H.integral hc C Ξ hΞ hGenerated := by
  let S := F.add C Ξ hΞ H
  obtain ⟨eF,heF⟩ := gamma_full_lift_density_graph_iso hc 𝔇 F.gamma
  obtain ⟨eH,heH⟩ := gamma_full_lift_density_graph_iso hc 𝔇 H.gamma
  obtain ⟨eS,heS⟩ := gamma_full_lift_density_graph_iso hc 𝔇 S.gamma
  have hsum := sum_full_lift_coprod_iso_gamma hc F.gamma H.gamma
  obtain ⟨f,hf⟩ := gamma_vf_iso_of_heq (family_realization_degree_eq n k)
    (family_density_graph_full_lift_realization_heq hc S.family)
    (vf_coprod_heq (family_realization_degree_eq n k) (family_density_graph_full_lift_realization_heq hc F.family)
      (family_density_graph_full_lift_realization_heq hc H.family))
    ((eS.symm hc 𝔇).trans hc 𝔇 ((sumFullLiftCoprodIso hc F.family H.family).trans hc 𝔇 (eF.coprod hc 𝔇 eH)))
    ((heS.symm hc 𝔇).trans hc 𝔇 (hsum.trans hc 𝔇 (heF.coprod hc 𝔇 heH)))
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  let A' := nativeMixedVolumeDomain hc H.family.densityGraph.domain
  let A'' := nativeMixedVolumeDomain hc S.family.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hA' : GammaSetDefinable 𝔅 (carrier A') := H.gamma.native_domain hc
  have hA'' : GammaSetDefinable 𝔅 (carrier A'') := S.gamma.native_domain hc
  have hW := realization_gamma hc C Ξ hΞ A hA F.family.densityGraph.selected F.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero
  have hW' := realization_gamma hc C Ξ hΞ A' hA' H.family.densityGraph.selected
    H.family.densityGraph.finite_selected (Fin.last H.arity) H.family.densityGraph_label_nonzero
  have hW'' := realization_gamma hc C Ξ hΞ A'' hA'' S.family.densityGraph.selected
    S.family.densityGraph.finite_selected (Fin.last S.arity) S.family.densityGraph_label_nonzero
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  let W := selectedCoordinateVolumeRealization hc A F.family.densityGraph.selected
    F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let W' := selectedCoordinateVolumeRealization hc A' H.family.densityGraph.selected
    H.family.densityGraph.finite_selected (Fin.last H.arity) H.family.densityGraph_label_nonzero
  let W'' := selectedCoordinateVolumeRealization hc A'' S.family.densityGraph.selected
    S.family.densityGraph.finite_selected (Fin.last S.arity) S.family.densityGraph_label_nonzero
  have hWc : VFVolumeObjectGamma (W.coprod W') 𝔅 := hW.coprod hW'
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  obtain ⟨EW',hEW',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W'.densityGraph.domain) hW'.densityGraph (Equiv.refl _)
  obtain ⟨EW'',hEW'',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W''.densityGraph.domain) hW''.densityGraph (Equiv.refl _)
  obtain ⟨EWc,hEWc,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc (W.coprod W').densityGraph.domain) hWc.densityGraph (Equiv.refl _)
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
  have h0 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A'' hA'' S.family.densityGraph.selected S.family.densityGraph.finite_selected (Fin.last S.arity)
    S.family.densityGraph_label_nonzero
    (S.contraction hc C Ξ hΞ hGenerated) (S.contraction_gamma hc C Ξ hΞ hGenerated) hW'' EW'' hEW''
  have h3 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    _ _ hW'' hWc f hf EW'' EWc hEW'' hEWc
  have h4 := GammaNamed.gamma_coprod_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    W W' hW hW' hWc EW EW' EWc hEW hEW' hEWc
  have h5 := CommonContextVolumeEquivalent.coprod hc (h1.symm hc) (h2.symm hc)
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    ((((h0.trans hc h3).trans hc h4).trans hc h5).descend hc 𝔇 hNames)

end IntegrationInACVF.Section7.GammaFun
