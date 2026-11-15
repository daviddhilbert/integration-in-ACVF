import Integration7.UniformCellShapePartitionArrays
import Integration7.StandardTernaryRestrictionVolumePartitions
import Integration7.UniformBalancedPartComparisons
import Integration7.UniformRectangularPartComparisons

/-! All three actual cell-family cases assemble for arbitrary specified
VF-two contraction orders. The normalized volume objects partition by
their original RV labels, with the literal retained density unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 4000000 in
theorem graph_family_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ) (hGenerated : VFGammaGeneratedBase G)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin (m+F.arity))
    (hδ : ∀ p : gammaRVGraphRefinement A F.parameters hNames, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (W : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let H := gammaRVGraphRefinement A F.parameters hNames
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfinH δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfinH δ hδ W hW) := by
  intro H hH hfinH hsmall
  let P := F.shapeNativePieces hNames
  let R := F.shapeRVLabels hNames
  let hP := F.shape_native_piece_gamma hNames
  let hR := F.shape_rv_labels_gamma hNames
  let hfinP := F.shape_native_piece_finite_labels hNames hfin
  have hδP (i : Fin 3) (p : P i) : (p.val.2 δ).val ≠ iRVZero :=
    hδ ⟨p.val,F.shape_native_piece_subset hNames i p.property⟩
  let DT (i : Fin 3) := Classical.choice (F.shape_contraction_presentations hNames T hT i)
  let DW (i : Fin 3) := Classical.choice (F.shape_contraction_presentations hNames W hW i)
  let XT := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    H hH hfinH δ hδ T hT
  let XW := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    H hH hfinH δ hδ W hW
  let YT (i : Fin 3) := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    (P i) (hP i) (hfinP i) δ (hδP i) (DT i).contraction (DT i).gamma
  let YW (i : Fin 3) := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    (P i) (hP i) (hfinP i) δ (hδP i) (DW i).contraction (DW i).gamma
  obtain ⟨eT,heT⟩ := standard_ternary_restriction_volume_partition C.uncountable.le C.saturated hsmall hc C hGC
    H P hH hP hfinH hfinP id R hR (F.shape_rv_labels_cover hNames) (F.shape_rv_labels_disjoint hNames)
    hNames T hT DT δ hδ hδP
  obtain ⟨eW,heW⟩ := standard_ternary_restriction_volume_partition C.uncountable.le C.saturated hsmall hc C hGC
    H P hH hP hfinH hfinP id R hR (F.shape_rv_labels_cover hNames) (F.shape_rv_labels_disjoint hNames)
    hNames W hW DW δ hδ hδP
  have hPartitionT : CommonContextVolumeEquivalent G C (((YT 0).coprod (YT 1)).coprod (YT 2)) XT := .of_iso eT heT
  have hPartitionW : CommonContextVolumeEquivalent G C (((YW 0).coprod (YW 1)).coprod (YW 2)) XW := .of_iso eW heW
  have hCompare (i : Fin 3) : CommonContextVolumeEquivalent G C (YT i) (YW i) := by
    fin_cases i
    · have h := zero_native_part_contractions_compare hc C hGC hNames F hfin δ (hδP 0)
        (DT 0).contraction (DW 0).contraction (DT 0).gamma (DW 0).gamma
      exact ⟨C,Set.Subset.refl _,h.extend (Set.Subset.refl _)⟩
    · exact rectangular_native_part_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric
        F hfin δ (hδP 1) (DT 1).contraction (DW 1).contraction (DT 1).gamma (DW 1).gamma
    · exact balanced_native_part_contractions_compare hc C hGC hNames hgamma hGenerated γ hγ hγ1 hGeneric
        F hfin δ (hδP 2) (DT 2).contraction (DW 2).contraction (DT 2).gamma (DW 2).gamma
  exact (hPartitionT.symm hc).trans hc
    (((hCompare 0).coprod hc (hCompare 1)).coprod hc (hCompare 2) |>.trans hc hPartitionW)

end IntegrationInACVF.Section7.UniformMixedCellPresentation
