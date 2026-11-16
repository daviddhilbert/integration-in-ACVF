module

public import Integration7.SelectedFamilyGeometricCommon
public import Integration7.OrderedAppendVolumeContractions

@[expose] public section

/-! Positive selected Lemma 7.5 for the actual density-graph families and
arbitrary ordered contraction programs, starting from the ordinary common
blowups of their genuine named VF fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a b l r k : ℕ}

set_option maxHeartbeats 2400000 in
theorem selected_family_ordered_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (T : OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc F.densityGraph.domain) U₀)
    (E : OrderedContractionProgram (C.base : Set M) (nativeMixedVolumeDomain hc G.densityGraph.domain) V₀)
    (hT : GammaProgramDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T)
    (hE : GammaProgramDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) E) :
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema U₀ (gamma_program_final_set T hT)
        (orderedAppendVolumeIndex T F.densityGraph.selected) (orderedAppendDensityIndex T (Fin.last a))).commonByGammaGeometry
      (gammaSelectedVolumeSchema V₀ (gamma_program_final_set E hE)
        (orderedAppendVolumeIndex E G.densityGraph.selected) (orderedAppendDensityIndex E (Fin.last b)))
      (fun j => (x j).val) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  let V := nativeMixedVolumeDomain hc G.densityGraph.domain
  have hU : GammaSetDefinable B (carrier U) := (gammaLogicInput B).real_set _ (setDefinable U)
  have hV : GammaSetDefinable B (carrier V) := (gammaLogicInput B).real_set _ (setDefinable V)
  exact lemma_7_5_ordered_geometric hc C C.uncountable.le C.saturated C.model00 C.small hΞ γ hγ hγ1
    (Set.Subset.refl _) U V hU hV F.densityGraph.selected G.densityGraph.selected (Fin.last a) (Fin.last b)
    (fun p hp => F.densityGraph_label_nonzero p hp) (fun p hp => G.densityGraph_label_nonzero p hp)
    F.densityGraph.finite_selected G.densityGraph.finite_selected
    (fun x => selected_densityGraph_geometric_common hc Ξ F G x (hCommon x)) T E hT hE

end IntegrationInACVF.Section7
