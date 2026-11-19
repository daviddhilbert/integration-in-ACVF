import Integration7.GammaFunLemma75
import Integration7.GammaNamedLiftSurjectivity
import Integration7.GammaNamedPullbackComparisons
import Integration7.GammaNamedUnaryChains
import Integration7.GammaNamedCorollary76
import Integration7.GammaNamedPreparedChains
import Integration7.IntegrationStandardContractionFormula

/-! **Gamma integration of a standard contraction.** Every Gamma positive VF
volume object is Gamma isomorphic to the lift of a Gamma RV object that is
common-context equivalent to any Gamma standard contraction of the object.
This is the Gamma form of the formula "integration of a VF class is the class
of its contraction". -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {k : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_lift_contraction_comparison (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hU : VFVolumeObjectGamma U G)
    {σ : Equiv.Perm (Fin (k+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (hE : GammaProgramDefinable G E.program) :
    ∃ P : GammaVolumeObjects G (C.base : Set M) k,
      (∃ e : VFVolumeIso U (rvVolumeLift P.val), e.GammaDefinable G) ∧
      CommonContextVolumeEquivalent G C P
        ⟨U.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC U hU E hE⟩ := by
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hA : GammaSetDefinable G (carrier A) := hU.densityGraph
  obtain ⟨b,B,T,hT,hBP⟩ := gamma_special_pullback_exists C hGC hNames hGenerated A hA
  have hB : GammaSetDefinable G (carrier B) := GammaChainDefinable.target G T.chain hT
  let δ := Fin.last U.arity
  have hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := by
    intro p
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact U.densityGraph.form.nonzero ⟨p.val,p.property⟩
      ((densityGraph_form_last U ⟨p.val,p.property⟩).trans hz)
  have hfinB := special_target_finite_labels C ∅ T U.densityGraph.finite_labels
  have hBF := special_pullback_volume_finite C ∅ T hBP U.densityGraph.finite_labels
  let ε := suffixIndex (special_chain_rvArity_le T.chain) δ
  have hε := special_retained_density_nonzero T δ hδ
  let P := pullbackCoordinateGammaObject hc C hGC B hB hBF ε hε
  let ψ := rawPullbackVolumeForm hc B hBP hBF ε hε
  let W := nativeMixedVFVolumeObject hc B hfinB ψ
  let V := nativeMixedVFVolumeObject hc A U.densityGraph.finite_labels U.densityGraph.form
  have hDensity : ∀ p, U.densityGraph.form.value p = ψ.value (rawSpecialMap hc T.toMap p) := by
    intro p
    rw [densityGraph_form_last,rawPullbackVolumeForm_density]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  let f : VFVolumeBijection U.densityGraph W := ⟨rawSpecialMap hc T.toMap,T.bijective,
    (special_preserves_volume hc C (Nat.zero_lt_succ k) T U.densityGraph.form ψ hDensity).1⟩
  let g : VFVolumeBijection W (rvVolumeLift P.val) := ⟨rawPullbackVolumeLiftMap hc B hBP,
    rawPullbackVolumeLiftMap_bijective hc B hBP,rawPullbackVolumeLiftMap_preserves hc C B hBP hBF ε hε⟩
  let fV := volumeDensityGraphBijection hc C U
  let h := fV.trans hc C (f.trans hc C g)
  have L := gammaLogicInput G
  have hAppend : GammaGraphDefinable G (vfMixedMapGraph fV.map) := by
    apply GammaGraphDefinable.congr (L.swap_graph hU.projection_graph)
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
  have hSpecial : GammaGraphDefinable G (vfMixedMapGraph f.map) :=
    vf_mixed_map_graph_raw_special hc T.toMap (GammaChainDefinable.graph L T.chain hT)
  have hCanon : GammaGraphDefinable G (vfMixedMapGraph g.map) := by
    have hc' := GammaPrimitiveDefinable.graph L (Primitive.canonical B) hB
    apply GammaGraphDefinable.congr hc'
    intro p q
    constructor
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
  have hIso : (VFVolumeIso.of_bijection h).GammaDefinable G := by
    refine ⟨hU.domain,gamma_rv_lift_carrier hc C hGC P.val P.property,?_⟩
    apply GammaGraphDefinable.congr (L.comp_graph hAppend (L.comp_graph hSpecial hCanon))
    intro p q
    constructor
    · rintro ⟨z,⟨u,rfl,rfl⟩,z',⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩
      have hv' : v = fV.map u := Subtype.ext hv
      have hw' : w = f.map v := Subtype.ext hw
      subst hv' hw'
      exact ⟨u,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨_,⟨u,rfl,rfl⟩,_,⟨_,rfl,rfl⟩,⟨_,rfl,rfl⟩⟩
  refine ⟨P,⟨VFVolumeIso.of_bijection h,hIso⟩,?_⟩
  -- comparison of contractions along U → V → W and the pullback object
  have hVdg : GammaSetDefinable G (volumeDensityGraph V.form).carrier :=
    gamma_coordinate_volume_density_graph hc hA V.form δ (fun p => densityGraph_form_last U ⟨p.val,p.property⟩)
  have hWdg : GammaSetDefinable G (volumeDensityGraph W.form).carrier :=
    gamma_coordinate_volume_density_graph hc hB W.form ε (rawPullbackVolumeForm_density hc B hBP hBF ε hε)
  have hV : VFVolumeObjectGamma V G := VFVolumeObjectGamma.of_density_graph hVdg
  have hW : VFVolumeObjectGamma W G := VFVolumeObjectGamma.of_density_graph hWdg
  let AV := nativeMixedVolumeDomain hc V.densityGraph.domain
  let AW := nativeMixedVolumeDomain hc W.densityGraph.domain
  obtain ⟨EV,hEV,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGenerated hGC AV hV.densityGraph
    (Equiv.refl _)
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGenerated hGC AW hW.densityGraph
    (Equiv.refl _)
  have hFirst := relative_volume_contractions_all_orders hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    U V hU hV fV hAppend 0 (fun _ _ _ => rfl) E EV hE hEV
  have hChain := gamma_special_unary_chain (Nat.zero_lt_succ k) T.chain hT
  have hData := gamma_unary_chain_volume_data_of_data hc C (specialUnaryChain (Nat.zero_lt_succ k) T.chain) hChain
    V.form W.form hVdg (special_unary_chain_volume_data hc C T V.form W.form hDensity) U.densityGraph.finite_labels
  have hMiddle := unary_chain_volume_contractions_compare hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    (specialUnaryChain (Nat.zero_lt_succ k) T.chain) hChain V.form W.form hVdg hWdg hData
    U.densityGraph.finite_labels hfinB hV hW EV EW hEV hEW
  have hLast := pullback_original_volume_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    B hB hBP hfinB hBF ψ ε (rawPullbackVolumeForm_density hc B hBP hBF ε hε) hW EW hEW
  exact ((hLast.trans hc (hMiddle.symm hc)).trans hc (hFirst.symm hc))

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

/-- **Contraction invariance.** Standard contractions of Gamma-isomorphic Gamma VF
volume objects are common-context equivalent. -/
theorem gamma_vf_iso_contraction_comparison (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hU : VFVolumeObjectGamma U G) (hV : VFVolumeObjectGamma V G)
    (f : VFVolumeIso U V) (hf : f.GammaDefinable G)
    {σ υ : Equiv.Perm (Fin (k+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E' : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) υ)
    (hE : GammaProgramDefinable G E.program) (hE' : GammaProgramDefinable G E'.program) :
    CommonContextVolumeEquivalent G C
      ⟨U.standardContractionObject hc C G.gamma E,standard_contraction_object_gamma hc C G hGC U hU E hE⟩
      ⟨V.standardContractionObject hc C G.gamma E',standard_contraction_object_gamma hc C G hGC V hV E' hE'⟩ := by
  obtain ⟨P,⟨eU,heU⟩,hPU⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    U hU E hE
  obtain ⟨Q,⟨eV,heV⟩,hQV⟩ := gamma_lift_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1
    V hV E' hE'
  have hPQ := rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 P Q
    ((eU.symm hc C).trans hc C (f.trans hc C eV)) ((heU.symm hc C).trans hc C (hf.trans hc C heV))
  exact ((hPU.symm hc).trans hc hPQ).trans hc hQV

end IntegrationInACVF.Section7.GammaNamed

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

set_option maxHeartbeats 3200000 in
/-- The selected standard contraction of a Gamma domain is common-context equivalent to
any Gamma standard contraction of its coordinate VF realization. -/
theorem gamma_selected_realization_contraction (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hA : GammaSetDefinable G (carrier A)) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)
    (hW : VFVolumeObjectGamma (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ) G)
    {υ : Equiv.Perm (Fin ((d+n)+1))}
    (EW : StandardContraction (nativeMixedVolumeDomain hc
      (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).densityGraph.domain) υ)
    (hEW : GammaProgramDefinable G EW.program) :
    CommonContextVolumeEquivalent G C
      ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfin T hT⟩
      ⟨(selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).standardContractionObject hc C G.gamma EW,
        standard_contraction_object_gamma hc C G hGC _ hW EW hEW⟩ := by
  let W := selectedCoordinateVolumeRealization hc A ρ hfin δ hδ
  obtain ⟨r,V,E,hE,hVF,hCon,hFull⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  let L := nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ
  have hL : GammaSetDefinable G (carrier L) := gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  have hfinL := native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin
  have hδL : ∀ p ∈ carrier L, (p.2 δ).val ≠ iRVZero := fun p hp =>
    native_program_selected_rv_vf_tail_density_nonzero hc A ρ δ (fun q => hδ q.val q.property) ⟨p,hp⟩
  let T' := selectedRVVFTailStandardContraction hc T ρ E
  have hT' := gamma_selected_rv_vf_tail_standard_contraction hc T ρ E hFull
  obtain ⟨E1,hE1,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGenerated hGC
    (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (selectedVFTailPermutation d σ)
  have hRet := retained_density_graph_contraction_comparison hc C G hGC hΞ hGeneric γ hγ hγ1 L hL hfinL W.form δ
    (fun _ => rfl) T' hT' hW E1 hE1
  have hNorm := raw_standard_volume_normalization hc C G hGC L hL hfinL δ hδL T' hT'
  have hTail := selected_tail_completion_common hc C G hGC A hA ρ hfin δ hδ T hT E hE hFull hVF hCon
  have hSame := gamma_vf_iso_contraction_comparison hc C G hGC hΞ hGenerated hNames hGeneric γ hγ hγ1 W W hW hW
    (VFVolumeIso.refl hc C W) (hW.refl_iso hc C) E1 EW hE1 hEW
  exact (((hTail.symm hc).trans hc hNorm).trans hc hRet).trans hc hSame

end IntegrationInACVF.Section7.GammaNamed
