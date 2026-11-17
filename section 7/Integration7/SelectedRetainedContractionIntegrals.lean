module

public import Integration7.SelectedRetainedVolumeSchemata
public import Integration7.SelectedFamilyGeometricCommon
public import Integration7.FieldBaseVolumeFamilyIntegrals
public import Integration7.PositiveSelectedContractionObjects
public import Integration7.CommonContextVolumeDescent

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A literally retained density can be integrated before adjoining a
second density graph. The actual appended contraction objects compare
by the nonempty-selected geometric theorem on their genuine named rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

set_option maxHeartbeats 2400000 in
theorem selected_retained_densityGraph_contractions_common
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ p ∈ F.domain.carrier, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) :
    VolumeBlowupEquivalent
      (standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc F.domain) F.selected δ hδ F.finite_selected T)
      (F.standardAppendObject hc Ξ E) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.domain
  let Z := nativeMixedVolumeDomain hc F.densityGraph.domain
  have hA := (gammaLogicInput B).real_set _ (setDefinable A)
  have hZ := (gammaLogicInput B).real_set _ (setDefinable Z)
  have hT := gamma_program_over_real_base B T.program
  have hE := gamma_program_over_real_base B E.program
  have hGeom := lemma_7_5_standard_geometric hc C C.uncountable.le C.saturated C.model00 C.small hΞ
    γ hγ hγ1 (Set.Subset.refl _) A Z hA hZ F.selected F.densityGraph.selected δ (Fin.last a)
    hδ F.densityGraph_label_nonzero F.finite_selected F.densityGraph.finite_selected
    (fun x => GammaRVVolumeSchema.commonInNamedContext_to_geometry hc _ _ _
      (selected_retained_densityGraph_named_common hc Ξ F δ hForm 0 0 x)) T E hT hE
  let U := standardAppendVolumeObject hc C Ξ A F.selected δ hδ F.finite_selected T
  let V := F.standardAppendObject hc Ξ E
  let z := fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val
  have hBase : (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M))=B := by
    simp [Set.range_eq_empty]
  have hU := standard_append_volume_object_gamma hc C Ξ A F.selected δ hδ F.finite_selected T
  have hV := standard_append_volume_object_gamma hc C Ξ Z F.densityGraph.selected (Fin.last a)
    F.densityGraph_label_nonzero F.densityGraph.finite_selected E
  have PU := standard_append_volume_object_schema_row hc C Ξ A F.selected δ hδ F.finite_selected T
  have PV := standard_append_volume_object_schema_row hc C Ξ Z F.densityGraph.selected (Fin.last a)
    F.densityGraph_label_nonzero F.densityGraph.finite_selected E
  have hBC : B.real ∪ Set.range z ⊆ (C.base : Set M) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using Set.Subset.refl (C.base : Set M)
  obtain ⟨D,hCD,h⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc C U V _ _ z PU PV
    (hBase.symm ▸ hU) (hBase.symm ▸ hV) hBC (hGeom Fin.elim0)
  have H : CommonContextVolumeEquivalent B C ⟨U,hU⟩ ⟨V,hV⟩ := ⟨D,hCD,h.rebase hBase⟩
  exact (H.descend hc C hNames).toOrdinary hc C B

theorem selected_family_field_appended_integral_retained_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (δ : Fin a)
    (hForm : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ p ∈ F.domain.carrier, (p.2 δ).val ≠ iRVZero)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.domain) (Equiv.refl _)) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase F =
      positiveVolumeBlowupClass hc C
        (standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc F.domain) F.selected δ hδ F.finite_selected T) := by
  apply (positiveVolumeBlowupClass_eq_iff hc C).mpr
  exact (selected_retained_densityGraph_contractions_common hc C Ξ hΞ hNames γ hγ hγ1 F δ hForm hδ T
    (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _))).symm hc C
end IntegrationInACVF.Section7
