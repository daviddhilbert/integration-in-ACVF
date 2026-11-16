module

public import Integration7.AERVVolumeFunctionIntegrals
public import Integration7.VolumeCoordinateChartInverses

@[expose] public section

/-! Almost-everywhere integration in coefficient-first appended order.
This is the convention compatible with successive head integration; it
is related to the VF-first realization by an explicit common permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_appended_integral_ae_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hAE : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩) :
    selectedFamilyIntegralValue hc C Ξ hGenerated F = selectedFamilyIntegralValue hc C Ξ hGenerated G := by
  let T := selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)
  let E := selectedFamilyIntegralContraction hc C Ξ hGenerated G (Equiv.refl _)
  have hNew := (positiveVolumeBlowupClass_eq_iff hc C).mp
    (selected_family_canonical_integral_ae_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F G hAE)
  have hCast := hNew.reindexDegree hc C (selected_append_degree_eq n k)
  let fF := selectedIntegralCoordinateChart hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
    F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T
  let fG := selectedIntegralCoordinateChart hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain)
    G.densityGraph.selected (Fin.last b) G.densityGraph_label_nonzero G.densityGraph.finite_selected E
  apply (positiveVolumeBlowupClass_eq_iff hc C).mpr
  exact hCast.of_permuted_coordinate_charts hc C (appendedToOriginalVolumePermutation (n+1) k).symm
    fF.symm fG.symm
    (finite_volume_coordinate_chart_inverse fF _
      (selected_integral_coordinate_chart_coordinates hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
        F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T))
    (finite_volume_coordinate_chart_inverse fG _
      (selected_integral_coordinate_chart_coordinates hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain)
        G.densityGraph.selected (Fin.last b) G.densityGraph_label_nonzero G.densityGraph.finite_selected E))
    (finite_volume_density_chart_inverse fF
      (selected_integral_coordinate_chart_density hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
        F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T))
    (finite_volume_density_chart_inverse fG
      (selected_integral_coordinate_chart_density hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain)
        G.densityGraph.selected (Fin.last b) G.densityGraph_label_nonzero G.densityGraph.finite_selected E))

def aeRVVolumeFunctionAppendedIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AERVVolumeFunction hc C n k → PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) :=
  Quotient.lift (fun F => selectedFamilyIntegralValue hc C Ξ hGenerated F.2)
    (fun F G h => selected_family_appended_integral_ae_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 G.2 h)

theorem ae_rv_volume_function_appended_integral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVolumeFunctionPresentation C (n+1) k) :
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ F) =
      selectedFamilyIntegralValue hc C Ξ hGenerated F.2 := rfl

end IntegrationInACVF.Section7
