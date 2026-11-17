module

public import Integration7.FiniteCoefficientContractionProductCharts
public import Integration7.SelectedRetainedContractionIntegrals
public import Integration7.FieldBaseUnarySpecialPreparations
public import Integration7.FieldBaseUnaryVolumeIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A positive coefficient times a finite-label unary volume object
has its actual degree-preserving product integral before normalization.
Both sides are computed using genuine original-base contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (RV carrier)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {d p : ℕ}

set_option maxHeartbeats 1600000 in
theorem finite_coefficient_unary_field_integral_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : PositiveVFVolumeObject (M := M) (C.base : Set M) 0)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M),
      {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase
      (finiteVolumeCoefficientFamily hc C F.densityGraph.domain F.densityGraph.finite_labels F.densityGraph.form R σ ε hR hε) =
    rvVolumeBlowupClassesProduct hc C (p+1) 1
      (positiveVolumeBlowupClass hc C (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε))
      (unaryFieldVolumeIntegral hc C Ξ FBase F) := by
  let A := F.densityGraph.domain
  let hA := F.densityGraph.finite_labels
  let ω := F.densityGraph.form
  let δ := Fin.last F.arity
  let hδ := unary_density_graph_label_nonzero F
  let J := finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε
  let U := nativeCoordinateDensityVolumeObject hc C R σ ε hR hε
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc A)
  obtain ⟨L⟩ := finite_coefficient_special_preparation_exists hc C A hA ω R σ ε hR hε Ξ hNames δ
    (densityGraph_form_last F) T hT hB
  let V := unaryPreparedFiniteHeadObject hc C Ξ T hB hT hA δ hδ
  have hHead : positiveVolumeBlowupClass hc C V=unaryFieldVolumeIntegral hc C Ξ FBase F :=
    ((unary_field_volume_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 F
      (unarySpecialStandardContraction T hB)).trans
      (positiveVolumeBlowupClass_iso hc C (unaryPreparedFiniteHeadIso hc C Ξ T hB hT hA δ hδ))).symm
  calc
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase J =
        positiveVolumeBlowupClass hc C (J.standardAppendObject hc Ξ (unarySpecialStandardContraction L.special L.pullback)) :=
      selected_family_field_appended_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 J _
    _ = positiveVolumeBlowupClass hc C (U.prod V) :=
      positiveVolumeBlowupClass_iso hc C
        (finiteCoefficientContractionProductIso hc C Ξ hNames A hA ω R σ ε hR hε δ hδ T hB hT L)
    _ = rvVolumeBlowupClassesProduct hc C (p+1) 1
        (positiveVolumeBlowupClass hc C U) (positiveVolumeBlowupClass hc C V) := rfl
    _ = _ := by rw [hHead]
end IntegrationInACVF.Section7
