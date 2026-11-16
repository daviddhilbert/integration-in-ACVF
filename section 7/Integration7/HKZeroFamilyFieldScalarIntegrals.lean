import Integration7.HKZeroFiniteCoefficientContractionCharts
import Integration7.HKNativeZeroCoefficientFieldIntegrals
import Integration7.HKZeroRVNativeDensityPresentations
import Integration7.HKZeroFamilyFiniteProductBijections
import Integration7.FieldBaseUnaryRetainedContractions
import Integration7.FieldBaseUnarySpecialPreparations

/-! Weighted finite factors commute with actual unary field-base
integration on zero-valued families. The result retains both forms
and uses no positive padding or cancellation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

set_option maxHeartbeats 1600000 in
theorem native_zero_finite_coefficient_field_integral
    (F : ZeroVFVolumeFamily C 1 a) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d) (ε : Fin d)
    (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    unaryFieldVolumeIntegral hc C Ξ FBase (nativeZeroFiniteCoefficientFamily hc C F R ε hR hε).fullVFObject =
      rvVolumeBlowupClass hc C (n := 0) (nativeZeroDensityObject hc C R ε hR hε) •
        unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject := by
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc F.domain)
  obtain ⟨L⟩ := native_zero_finite_coefficient_special_preparation_exists hc C F R ε hR hε Ξ hNames δ hF T hT hB
  let J := nativeZeroFiniteCoefficientFamily hc C F R ε hR hε
  let Z := nativeZeroDensityObject hc C R ε hR hε
  let V := unaryPreparedFiniteHeadObject hc C Ξ T hB hT F.finite_labels δ hδ
  have hRaw := unary_field_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1
    (nativeMixedVolumeDomain hc F.domain) F.finite_labels F.form δ hF hδ
    (unarySpecialStandardContraction T hB)
  have hHeadF : positiveVolumeBlowupClass hc C V=unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject :=
    (positiveVolumeBlowupClass_iso hc C
      (unaryPreparedFiniteHeadIso hc C Ξ T hB hT F.finite_labels δ hδ)).symm.trans hRaw
  calc
    unaryFieldVolumeIntegral hc C Ξ FBase J.fullVFObject =
        positiveVolumeBlowupClass hc C (rawStandardVolumeObject hc C Ξ
          (nativeMixedVolumeDomain hc J.fullVFObject.densityGraph.domain)
          J.fullVFObject.densityGraph.finite_labels (Fin.last (a+d))
          (unary_density_graph_label_nonzero J.fullVFObject) (unarySpecialStandardContraction L.special L.pullback)) :=
      unary_field_volume_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 J.fullVFObject _
    _ = positiveVolumeBlowupClass hc C (zeroProduct Z V) :=
      positiveVolumeBlowupClass_iso hc C
        (zeroFiniteCoefficientContractionProductIso hc C Ξ hNames F R ε hR hε δ hδ T hB hT L)
    _ = rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C V :=
      (weighted_zero_smul_representative hc C Z V).symm
    _ = _ := by rw [hHeadF]

set_option maxHeartbeats 1600000 in
theorem zero_family_unary_field_integral_weighted_coefficient
    (F : ZeroVFVolumeFamily C 1 a) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    unaryFieldVolumeIntegral hc C Ξ FBase (F.prodZero Z).fullVFObject =
      rvVolumeBlowupClass hc C (n := 0) Z • unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject := by
  let V := zeroRVNativeDensityObject hc C Z
  let e := zeroRVNativeDensityIso hc C Z
  have hZ : rvVolumeBlowupClass hc C (n := 0) Z=rvVolumeBlowupClass hc C (n := 0) V := Quotient.sound ⟨e⟩
  have hGraph := unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1 _ _
    (volumeDensityGraphBijection hc C F.fullVFObject)
  calc
    unaryFieldVolumeIntegral hc C Ξ FBase (F.prodZero Z).fullVFObject =
        unaryFieldVolumeIntegral hc C Ξ FBase (F.prodZero V).fullVFObject :=
      unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1 _ _
        (zeroFamilyFiniteProductBijection hc C F F Z V (Map.id _) Function.bijective_id
          (fun _ => rfl) (fun _ => rfl) e)
    _ = unaryFieldVolumeIntegral hc C Ξ FBase (F.densityGraph.prodZero V).fullVFObject :=
      (unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1 _ _
        (zeroFamilyDensityGraphProductBijection hc C F V)).symm
    _ = rvVolumeBlowupClass hc C (n := 0) V • unaryFieldVolumeIntegral hc C Ξ FBase F.densityGraph.fullVFObject :=
      native_zero_finite_coefficient_field_integral hc C Ξ hΞ FBase hNames γ hγ hγ1 F.densityGraph
        (Fin.last a) (densityGraph_form_last F.fullVFObject) (unary_density_graph_label_nonzero F.fullVFObject)
        (zeroRVNativeDensityDomain hc C Z) (Fin.last Z.underlying.obj.arity)
        (ordinary_rv_native_labels_finite hc C Z.densityGraph.underlying) (zero_rv_native_density_nonzero hc C Z)
    _ = _ := congrArg₂ (fun z v => z • v) hZ.symm hGraph.symm

end IntegrationInACVF.Section7.HK
