module

public import Integration7.AppendedContractionVolumeObjects
public import Integration7.GeometricVolumeCommonOnObjects
public import Integration7.GammaVolumeBaseEquality

@[expose] public section

/-! Positive selected Lemma 7.5 on the specified actual contraction
objects. The full density-graph labels are retained, and all common
blowup chains and charts are supplied by the theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (VF)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a b k : ℕ}

def SelectedVFVolumeFamily.standardAppendObject
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C n a k)
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree n k) :=
  standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
    F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T

set_option maxHeartbeats 2400000 in
theorem lemma_7_5_positive_objects
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) σ) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let U := F.standardAppendObject hc Ξ T
    let V := G.standardAppendObject hc Ξ E
    ∃ (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B),
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (appendVolumeDegree n k)
        ⟨U.extend hCD,hU.extend hCD⟩ ⟨V.extend hCD,hV.extend hCD⟩ := by
  intro B U V
  have hU : VolumeObjectGamma U B := standard_append_volume_object_gamma hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero
    F.densityGraph.finite_selected T
  have hV : VolumeObjectGamma V B := standard_append_volume_object_gamma hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain) G.densityGraph.selected (Fin.last b) G.densityGraph_label_nonzero
    G.densityGraph.finite_selected E
  let hT := gamma_program_over_real_base B T.program
  let hE := gamma_program_over_real_base B E.program
  let LF := gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
    (orderedAppendVolumeIndex T.program F.densityGraph.selected) (orderedAppendDensityIndex T.program (Fin.last a))
  let RF := gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE)
    (orderedAppendVolumeIndex E.program G.densityGraph.selected) (orderedAppendDensityIndex E.program (Fin.last b))
  let z : Fin 0 → M := fun i => (Fin.elim0 i : VF (M := M)).val
  have hBase : (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = B := by
    change (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = ⟨B.real,B.gamma⟩
    rw [Set.range_eq_empty,Set.union_empty]
  have PU : RVVolumeSchemaRow U LF z := standard_append_volume_object_schema_row hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) F.densityGraph.selected (Fin.last a)
    F.densityGraph_label_nonzero F.densityGraph.finite_selected T
  have PV : RVVolumeSchemaRow V RF z := standard_append_volume_object_schema_row hc C Ξ (nativeMixedVolumeDomain hc G.densityGraph.domain) G.densityGraph.selected (Fin.last b)
    G.densityGraph_label_nonzero G.densityGraph.finite_selected E
  have hU' : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩ := hBase.symm ▸ hU
  have hV' : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩ := hBase.symm ▸ hV
  have hBC : B.real ∪ Set.range z ⊆ (C.base : Set M) := by
    simpa only [Set.range_eq_empty,Set.union_empty] using (Set.Subset.refl (C.base : Set M))
  obtain ⟨D,hCD,h⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc C U V LF RF z PU PV hU' hV' hBC
    (lemma_7_5_positive hc C Ξ hΞ γ hγ hγ1 F G hCommon T E Fin.elim0)
  refine ⟨hU,hV,D,hCD,?_⟩
  exact h.rebase hBase

end IntegrationInACVF.Section7
