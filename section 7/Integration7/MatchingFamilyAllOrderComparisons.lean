module

public import Integration7.MatchingFamilyOppositeContractions

@[expose] public section

/-! All specified VF-two orders on the actual matching family have
the full original-Gamma volume blowup comparison. The two same-order
cases useCorollary7.6; the opposite cases use the proved translations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

set_option maxHeartbeats 3600000 in
theorem matching_family_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))
    (hδ : ∀ p : P.inFixedContext.matchingPreparedFamily, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) σ)
    (W : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let Q := P.inFixedContext
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingPreparedFamily Q.baseInclusion) Q.matching_prepared_family_gamma hfinH δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingPreparedFamily Q.baseInclusion) Q.matching_prepared_family_gamma hfinH δ hδ W hW) := by
  intro Q hsmall hfinH
  rcases vf_two_order_cases σ with rfl | rfl
  · rcases vf_two_order_cases τ with rfl | rfl
    · exact retained_density_same_order_contractions_compare hc C C.uncountable.le C.saturated hsmall
        hgamma γ hγ hγ1 hGC hGeneric (extendBase Q.matchingPreparedFamily Q.baseInclusion)
        Q.matching_prepared_family_gamma hfinH δ hδ T W hT hW
    · exact matching_family_opposite_contractions_compare hc hGC hgamma γ hγ hγ1 hGeneric
        P hNonzero hfin δ hδ T W hT hW
  · rcases vf_two_order_cases τ with rfl | rfl
    · have h := matching_family_opposite_contractions_compare hc hGC hgamma γ hγ hγ1 hGeneric
        P hNonzero hfin δ hδ W T hW hT
      exact CommonContextVolumeEquivalent.symm hc h
    · exact retained_density_same_order_contractions_compare hc C C.uncountable.le C.saturated hsmall
        hgamma γ hγ hγ1 hGC hGeneric (extendBase Q.matchingPreparedFamily Q.baseInclusion)
        Q.matching_prepared_family_gamma hfinH δ hδ T W hT hW

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
