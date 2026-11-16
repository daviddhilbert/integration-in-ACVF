module

public import Integration7.MixedCellGraphRefinements
public import Integration7.RVGraphRefinementContractionComparisons

@[expose] public section

/-! Reduction of arbitrary specified VF² standard contractions to
specified contractions on one actual definable two-cell family. The
same retained density is used on both actual normalized output objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}

theorem two_cell_contraction_reduction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) 2 a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    let hreal : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    ∃ d : ℕ, ∃ P : GammaRVMap B (carrier A) d,
      ParameterizedCells.DefinableTwoCell B (carrier (gammaRVGraphRefinement A P hNames)) ∧
      let H := gammaRVGraphRefinement A P hNames
      let hH := gamma_rv_graph_refinement_target_gamma A P hNames
      let hfinH := gamma_rv_graph_refinement_finite_labels A hfin P hNames
      let hε := rv_graph_refinement_density_nonzero A P hNames δ hδ
      ∀ (σ : Equiv.Perm (Fin 2)) (T : StandardContraction A σ) (E : StandardContraction H σ)
      (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program),
      let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC A hA hfin δ hδ T hT
      let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC H hH hfinH (Fin.castAdd d δ) hε E hE
      ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
        GammaVolumeBlowupEquivalent B (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro hreal
  obtain ⟨d,P,hCell⟩ := gamma_two_cell_graph_refinement_exists C.uncountable.le C.saturated C.model00
    hreal hGenerated γ hγ hγ1 A hA hNames
  refine ⟨d,P,hCell,?_⟩
  intro H hH hfinH hε σ T E hT hE U V
  exact rv_graph_refinement_contraction_common_blowup hc C C.uncountable.le C.saturated hreal hgamma
    γ hγ hγ1 hBC hNames hGeneric A hA hfin P δ hδ T E hT hE

end IntegrationInACVF.Section7
