module

public import Integration7.VolumeIntegrationEquivalence
public import Integration7.PositiveVolumeLiftSurjectivity
public import Integration7.UnaryChainVolumeContractions
public import Integration7.PullbackOriginalVolumeClasses
public import Integration7.SpecialRetainedVolumeChains
public import Integration7.CommonContextVolumeDescent

@[expose] public section

/-! Integration of an actual VF volume object can be computed by any
specified standard contraction of its density graph, in any VF order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier GammaSetDefinable gammaLogicInput setDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

set_option maxHeartbeats 2400000 in
theorem positive_volume_integration_standard_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) n)
    {σ : Equiv.Perm (Fin (n+1))}
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (positiveVFVolumeIsoClass hc C U) =
      positiveVolumeBlowupClass hc C (U.standardContractionObject hc C Ξ E) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  obtain ⟨b,B,⟨T⟩,hBP⟩ := SpecialTransformations.Section5.Paper.corollary_5_6 C.saturated C.model00 C.small A
  let δ := Fin.last U.arity
  have hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := by
    intro p
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact U.densityGraph.form.nonzero ⟨p.val,p.property⟩
      ((densityGraph_form_last U ⟨p.val,p.property⟩).trans hz)
  have hfinB := special_target_finite_labels C Ξ T U.densityGraph.finite_labels
  have hBF := special_pullback_volume_finite C Ξ T hBP U.densityGraph.finite_labels
  let ε := suffixIndex (special_chain_rvArity_le T.chain) δ
  have hε := special_retained_density_nonzero T δ hδ
  let P := pullbackCoordinateVolumeObject hc B hBF ε hε
  let ψ := rawPullbackVolumeForm hc B hBP hBF ε hε
  let V := nativeMixedVFVolumeObject hc A U.densityGraph.finite_labels U.densityGraph.form
  let W := nativeMixedVFVolumeObject hc B hfinB ψ
  have hDensity : ∀ p, V.form.value p = ψ.value (rawSpecialMap hc T.toMap p) := by
    intro p
    change U.densityGraph.form.value p = (rawPullbackVolumeForm hc B hBP hBF ε hε).value
      (rawSpecialMap hc T.toMap p)
    rw [densityGraph_form_last,rawPullbackVolumeForm_density]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  let f : VFVolumeBijection V W := ⟨rawSpecialMap hc T.toMap,T.bijective,
    (special_preserves_volume hc C (Nat.zero_lt_succ n) T V.form ψ hDensity).1⟩
  let g : VFVolumeBijection W (rvVolumeLift P) := ⟨rawPullbackVolumeLiftMap hc B hBP,
    rawPullbackVolumeLiftMap_bijective hc B hBP,rawPullbackVolumeLiftMap_preserves hc C B hBP hBF ε hε⟩
  let fV : VFVolumeBijection U V := volumeDensityGraphBijection hc C U
  have hIntegral : positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C U) = positiveVolumeBlowupClass hc C P :=
    (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 U P).mpr
      ((positiveVFVolumeIsoClass_eq_iff hc C).mpr
        ⟨VFVolumeIso.of_bijection (fV.trans hc C (f.trans hc C g))⟩)
  let AV := nativeMixedVolumeDomain hc V.densityGraph.domain
  let AW := nativeMixedVolumeDomain hc W.densityGraph.domain
  have hAV : GammaSetDefinable G (carrier AV) := (gammaLogicInput G).real_set _ (setDefinable AV)
  have hAW : GammaSetDefinable G (carrier AW) := (gammaLogicInput G).real_set _ (setDefinable AW)
  obtain ⟨EV,hEV,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 C.small hGenerated (Set.Subset.refl _) AV hAV (Equiv.refl _)
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := G)
    C.saturated C.model00 C.small hGenerated (Set.Subset.refl _) AW hAW (Equiv.refl _)
  have hFirst := relative_volume_contractions_all_orders hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    U V fV 0 (fun _ _ _ => rfl) E EV
  have hMiddle := unary_chain_volume_contractions_compare hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (specialUnaryChain (Nat.zero_lt_succ n) T.chain) V.form W.form
    (special_unary_chain_volume_data hc C T V.form W.form hDensity)
    U.densityGraph.finite_labels hfinB EV EW
  have hLast := pullback_original_volume_contraction_comparison hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    B hBP hfinB hBF ψ ε (rawPullbackVolumeForm_density hc B hBP hBF ε hε) EW
  have hCommon := (hFirst.trans hc hMiddle).trans hc (hLast.symm hc)
  have hOriginal := (hCommon.descend hc C hNames).toOrdinary hc C G
  exact hIntegral.trans ((positiveVolumeBlowupClass_eq_iff hc C).mpr hOriginal).symm

end IntegrationInACVF.Section7
