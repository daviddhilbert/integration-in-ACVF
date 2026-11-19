import Integration7.GammaNamedLiftCharts

/-! The Gamma-named Proposition 7.8 kernel for coordinate densities: Gamma RV
volume objects whose densities are RV coordinates and a Gamma almost
everywhere VF volume isomorphism of their lifts are Gamma-named
common-context equivalent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (pullbackObject_finiteVolume GammaSetDefinable carrier)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem rv_volume_lift_coordinate_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (hTransport : GammaVolumeTransportInput hc G (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U G) (hV : VolumeObjectGamma V G)
    (δ : Fin U.underlying.obj.arity) (ε : Fin V.underlying.obj.arity)
    (hUδ : ∀ u, U.form.value u = u.val δ) (hVε : ∀ v, V.form.value v = v.val ε)
    (f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) (hf : f.GammaDefinable G) :
    CommonContextVolumeEquivalent G C ⟨U,hU⟩ ⟨V,hV⟩ := by
  let A := actualRVVolumeLiftPresentation hc U.underlying.obj
  let B := actualRVVolumeLiftPresentation hc V.underlying.obj
  have hA := gamma_actual_lift_presentation hc C hGC U hU
  have hB := gamma_actual_lift_presentation hc C hGC V hV
  let ω := (actualRVVolumeLiftChartObject hc U).form
  let π := (actualRVVolumeLiftChartObject hc V).form
  have hfinA := actual_rv_volume_lift_finite_labels hc U
  have hfinB := actual_rv_volume_lift_finite_labels hc V
  have hδ := actual_rv_volume_lift_chart_nonzero hc U δ hUδ
  have hε := actual_rv_volume_lift_chart_nonzero hc V ε hVε
  have hAP := typedLift_pullback (normalizedActualRVObject hc U.underlying.obj)
  have hBP := typedLift_pullback (normalizedActualRVObject hc V.underlying.obj)
  have hAF := pullbackObject_finiteVolume A hAP hfinA
  have hBF := pullbackObject_finiteVolume B hBP hfinB
  let f' := (VFVolumeIso.of_bijection (actualRVVolumeLiftChart hc C U)).trans hc C
    (f.trans hc C ((VFVolumeIso.of_bijection (actualRVVolumeLiftChart hc C V)).symm hc C))
  have hf' : f'.GammaDefinable G :=
    (actual_rv_volume_lift_chart_gamma hc C hGC U hU).trans hc C
      (hf.trans hc C ((actual_rv_volume_lift_chart_gamma hc C hGC V hV).symm hc C))
  have hMiddle := pullback_volume_ae_kernel hc C G hGC hΞ hGenerated hNames hGeneric hTransport γ hγ hγ1
    A B hA hB hAP hBP hfinA hfinB hAF hBF ω π δ ε
    (actual_rv_volume_lift_chart_density hc U δ hUδ) (actual_rv_volume_lift_chart_density hc V ε hVε)
    hδ hε f' hf'
  have hLeft : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC A hA hAF δ hδ) ⟨U,hU⟩ :=
    .of_iso (actualRVVolumePullbackIso hc C U δ hUδ hδ)
      (actual_rv_volume_pullback_iso_gamma hc C hGC U hU δ hUδ hδ)
  have hRight : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C hGC B hB hBF ε hε) ⟨V,hV⟩ :=
    .of_iso (actualRVVolumePullbackIso hc C V ε hVε hε)
      (actual_rv_volume_pullback_iso_gamma hc C hGC V hV ε hVε hε)
  exact (hLeft.symm hc).trans hc (hMiddle.trans hc hRight)

end IntegrationInACVF.Section7.GammaNamed
