import Integration7.BalancedGraphFamilyAllOrderComparisons
import Integration7.SelectedBalancedParadigms
import Integration7.NativeCellFamilyPartitionDomains

/-! The actual balanced part of the original cell-family partition
has the whole all-order volume comparison. Its balanced rows and
nonzero paradigms are derived from that actual partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 2000000 in
theorem balanced_native_part_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ) (hGenerated : VFGammaGeneratedBase G)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin (m+F.arity))
    (hδ : ∀ p : F.balancedNativeRefinement hNames, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (F.balancedNativeRefinement hNames) σ)
    (W : StandardContraction (F.balancedNativeRefinement hNames) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (F.balancedNativeRefinement hNames) (F.balanced_native_refinement_gamma hNames)
        (F.balanced_native_refinement_finite_labels hNames hfin) δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (F.balancedNativeRefinement hNames) (F.balanced_native_refinement_gamma hNames)
        (F.balanced_native_refinement_finite_labels hNames hfin) δ hδ W hW) :=
  balanced_graph_family_contractions_compare hc C hGC hNames hgamma hGenerated γ hγ hγ1 hGeneric
    (F.balancedNativeChart hNames) (F.balanced_native_chart_rows hNames γ hγ1)
    (F.balanced_native_chart_paradigm_nonzero hNames) (F.balanced_native_source_finite_labels hNames hfin)
    δ hδ T W hT hW

end IntegrationInACVF.Section7.UniformMixedCellPresentation
