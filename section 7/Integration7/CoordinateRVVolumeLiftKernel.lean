module

public import Integration7.PullbackVolumeAEKernel
public import Integration7.ActualRVVolumeLiftCharts
public import Integration7.VFVolumeComposition
public import Integration7.RealVolumeGammaCertificates
public import Integration7.GammaTermContextVolumeGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The lift kernel on the original RV volume objects when their
densities are literal retained coordinates. All witness geometry retains
the original Gamma base in a common containing real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (pullbackObject_finiteVolume gammaLogicInput setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem rv_volume_lift_coordinate_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (δ : Fin U.underlying.obj.arity) (ε : Fin V.underlying.obj.arity)
    (hU : ∀ u, U.form.value u = u.val δ) (hV : ∀ v, V.form.value v = v.val ε)
    (f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) :
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      ⟨U,volume_object_gamma_over_real_base hc C Ξ U⟩ ⟨V,volume_object_gamma_over_real_base hc C Ξ V⟩ := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := actualRVVolumeLiftPresentation hc U.underlying.obj
  let B := actualRVVolumeLiftPresentation hc V.underlying.obj
  let ω := (actualRVVolumeLiftChartObject hc U).form
  let π := (actualRVVolumeLiftChartObject hc V).form
  have hfinA := actual_rv_volume_lift_finite_labels hc U
  have hfinB := actual_rv_volume_lift_finite_labels hc V
  have hδ := actual_rv_volume_lift_chart_nonzero hc U δ hU
  have hε := actual_rv_volume_lift_chart_nonzero hc V ε hV
  have hAP := typedLift_pullback (normalizedActualRVObject hc U.underlying.obj)
  have hBP := typedLift_pullback (normalizedActualRVObject hc V.underlying.obj)
  have hAF := pullbackObject_finiteVolume A hAP hfinA
  have hBF := pullbackObject_finiteVolume B hBP hfinB
  let f' := (VFVolumeIso.of_bijection (actualRVVolumeLiftChart hc C U)).trans hc C
    (f.trans hc C ((VFVolumeIso.of_bijection (actualRVVolumeLiftChart hc C V)).symm hc C))
  have hMiddle := pullback_volume_ae_kernel hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    A B hAP hBP hfinA hfinB hAF hBF ω π δ ε
    (actual_rv_volume_lift_chart_density hc U δ hU) (actual_rv_volume_lift_chart_density hc V ε hV) hδ hε f'
  let eU := actualRVVolumePullbackIso hc C U δ hU hδ
  let eV := actualRVVolumePullbackIso hc C V ε hV hε
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  have hLeft : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) A
        ((gammaLogicInput G).real_set _ (setDefinable A)) hAF δ hδ)
      ⟨U,volume_object_gamma_over_real_base hc C Ξ U⟩ :=
    .of_iso eU (eU.gamma_of_term_context hc C hBase)
  have hRight : CommonContextVolumeEquivalent G C
      (pullbackCoordinateGammaObject hc C (Set.Subset.refl _) B
        ((gammaLogicInput G).real_set _ (setDefinable B)) hBF ε hε)
      ⟨V,volume_object_gamma_over_real_base hc C Ξ V⟩ :=
    .of_iso eV (eV.gamma_of_term_context hc C hBase)
  exact (hLeft.symm hc).trans hc (hMiddle.trans hc hRight)

end IntegrationInACVF.Section7
