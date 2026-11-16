module

public import Integration7.OrdinaryFiniteCoefficientContractionCharts
public import Integration7.OrdinaryUnitGraphProductBijections
public import Integration7.FieldBaseUnaryRetainedContractions
public import Integration7.FieldBaseUnarySpecialPreparations
public import Integration7.PositiveVolumeProductOrdinaryScalars

@[expose] public section

/-! Actual ordinary RV[0] coefficients commute with the unary field-base
integral of ordinary-valued families. A degree-one raw contraction chart
proves the identity directly, with no point padding or cancellation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

set_option maxHeartbeats 2400000 in
theorem ordinary_family_unary_field_integral_ordinary_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C 1 a) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    unaryFieldVolumeIntegral hc C Ξ FBase (F.prodZero Z).fullVFObject =
      rvVolumeBlowupClass hc C (n := 0) Z • unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject := by
  let H := F.unitSelectedFamily
  let hfin := F.fullVFObject.densityGraph.finite_labels
  let δ := Fin.last a
  let hδ := unary_density_graph_label_nonzero F.fullVFObject
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc H.domain)
  obtain ⟨L⟩ := ordinary_coefficient_special_preparation_exists hc C Ξ hNames H Z T hT hB
  let J := H.prodZero Z
  let O := F.unitGraph.prodZero Z
  let A := nativeMixedVolumeDomain hc J.domain
  let δJ := Fin.castAdd Z.obj.arity δ
  let hδJ := fun q hq => ordinary_coefficient_retained_density_nonzero C H Z δ hδ ⟨q,hq⟩
  let S := unarySpecialStandardContraction L.special L.pullback
  let ω := VolumeForm.one (SpecialTransformations.Section9.rawSpecialSet hc A)
  have hω (q : SpecialTransformations.Section9.rawSpecialSet hc A) : ω.value q=q.val.2 δJ := by
    have h := (mem_mixed_rv_factor_domain H.domain Z.obj.domain q.val.1 q.val.2).mp q.property
    exact (ordinary_unit_selected_density_label F ⟨(q.val.1,q.val.2 ∘ Fin.castAdd Z.obj.arity),h.1⟩).symm
  have hRaw := unary_field_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 A O.finite_labels ω δJ hω hδJ S
  let Z₀ := nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z)
  let V := unaryPreparedFiniteHeadObject hc C Ξ T hB hT hfin δ hδ
  have hVF : unaryFieldVolumeIntegral hc C Ξ FBase F.fullVFObject=positiveVolumeBlowupClass hc C V :=
    (unary_field_volume_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 F.fullVFObject
      (unarySpecialStandardContraction T hB)).trans
      (positiveVolumeBlowupClass_iso hc C (unaryPreparedFiniteHeadIso hc C Ξ T hB hT hfin δ hδ))
  calc
    unaryFieldVolumeIntegral hc C Ξ FBase (F.prodZero Z).fullVFObject =
        unaryFieldVolumeIntegral hc C Ξ FBase O.fullVFObject :=
      (unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1 _ _
        (ordinaryUnitGraphProductVolumeBijection hc C F Z)).symm
    _ = positiveVolumeBlowupClass hc C (rawStandardVolumeObject hc C Ξ A O.finite_labels δJ hδJ S) := hRaw.symm
    _ = positiveVolumeBlowupClass hc C (PositiveRVVolumeObject.zero_prod Z₀ V) :=
      positiveVolumeBlowupClass_iso hc C (ordinaryFiniteCoefficientContractionIso hc C Ξ hNames H Z hfin δ hδ T hB hT L)
    _ = positiveVolumeBlowupClass hc C (V.prod_zero Z₀) :=
      (positiveVolumeBlowupClass_iso hc C (volumeZeroProductSwapIso hc C V Z₀)).symm
    _ = rvVolumeBlowupClass hc C (n := 0) Z₀ • positiveVolumeBlowupClass hc C V :=
      (ordinary_volume_smul_representative hc C Z₀ V).symm
    _ = _ := by rw [ordinary_rv_native_class,← hVF]
end IntegrationInACVF.Section7
