module

public import Integration7.PointwiseRVVolumeFunctions
public import Integration7.SelectedIntegralCoordinateCharts
public import Integration7.SelectedCoordinateVolumeRealizations

@[expose] public section

/-! The VF-first integral of a positive homogeneous RV-volume family.
Its pointwise representative independence follows from the actual7.5
comparison and the explicit common coordinate permutation. Its value is
the integration of a genuine full VF realization with retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

def SelectedVFVolumeFamily.canonicalIntegralObject
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    {σ : Equiv.Perm (Fin (n+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) ((k+1)+n) :=
  selectedStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
    F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T

theorem selected_family_canonical_integral_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) (Equiv.refl _))
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) (Equiv.refl _)) :
    VolumeBlowupEquivalent (F.canonicalIntegralObject hc Ξ T) (G.canonicalIntegralObject hc Ξ E) := by
  have hOld := selected_family_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F G hCommon T E
  have hNew := hOld.of_permuted_coordinate_charts hc C (appendedToOriginalVolumePermutation (n+1) k)
    (selectedIntegralCoordinateChart hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected (Fin.last a)
      F.densityGraph_label_nonzero F.densityGraph.finite_selected T)
    (selectedIntegralCoordinateChart hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain) G.densityGraph.selected (Fin.last b)
      G.densityGraph_label_nonzero G.densityGraph.finite_selected E)
    (selected_integral_coordinate_chart_coordinates hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected (Fin.last a)
      F.densityGraph_label_nonzero F.densityGraph.finite_selected T)
    (selected_integral_coordinate_chart_coordinates hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain) G.densityGraph.selected (Fin.last b)
      G.densityGraph_label_nonzero G.densityGraph.finite_selected E)
    (selected_integral_coordinate_chart_density hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected (Fin.last a)
      F.densityGraph_label_nonzero F.densityGraph.finite_selected T)
    (selected_integral_coordinate_chart_density hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain) G.densityGraph.selected (Fin.last b)
      G.densityGraph_label_nonzero G.densityGraph.finite_selected E)
  exact hNew.of_reindexDegree hc C (selected_append_degree_eq n k)

def selectedFamilyCanonicalIntegralValue
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) : PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  positiveVolumeBlowupClass hc C
    (F.canonicalIntegralObject hc Ξ (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)))

theorem selected_family_canonical_integral_value_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated G :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_canonical_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F G hCommon
      (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _))
      (selectedFamilyIntegralContraction hc C Ξ hGenerated G (Equiv.refl _)))

def SelectedVFVolumeFamily.canonicalVFRealization
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) ((k+1)+n) :=
  selectedCoordinateVolumeRealization hc (nativeMixedVolumeDomain hc F.densityGraph.domain)
    F.densityGraph.selected F.densityGraph.finite_selected (Fin.last a) F.densityGraph_label_nonzero

theorem selected_family_canonical_integral_realization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C (F.canonicalVFRealization hc)) :=
  (selected_coordinate_volume_realization_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected F.densityGraph.finite_selected
    (Fin.last a) F.densityGraph_label_nonzero
    (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _))).symm

end IntegrationInACVF.Section7
