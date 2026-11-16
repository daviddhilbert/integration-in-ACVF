module

public import Integration7.MixedCellGraphRefinements
public import Integration7.GammaDefinableNameContexts
public import Integration7.TwoCellContractionReduction

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

theorem gamma_named_two_cell_contraction_reduction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hB0 : B.real ⊆ (C0.base : Set M)) (hBase : B.real = (C0.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C0.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ) :
    let C := gammaDefinableNamesVolumeContext hc C0 B hB0 hgamma
    let hBC : B.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_definable_names_context_contains hc C0 B hB0 hgamma (Or.inl (hB0 hx))
    let hNames : commonRealNames B ⊆ (C.base : Set M) := fun _ hx =>
      gamma_definable_names_context_contains hc C0 B hB0 hgamma (Or.inr hx)
    ∀ (A : DefSet (M := M) (C.base : Set M) 2 a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero),
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
  intro C hBC hNames A hA hfin δ hδ
  exact two_cell_contraction_reduction hc C hBC hNames hgamma hGenerated γ hγ hγ1
    (fun x hx => gamma_definable_names_context_preserves_independence hc C0 B hB0 hgamma hBase x hx)
    A hA hfin δ hδ

end IntegrationInACVF.Section7
