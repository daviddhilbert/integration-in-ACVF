module

public import Integration7.TwoPartialVolumeRowComparisons
public import Integration7.TwoHeadTailVolumeSelectors
public import Integration7.GenericOrderedAppendVolumeContractions
public import Integration7.OrderedAppendVolumeFiniteness
public import Integration7.SelectedVolumeDegreeTransport

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Higher-dimensional first-two-coordinate exchange for actual ordered
programs. The two retained VF tags give the positive selected degree
required by Lemma7.5; every remaining VF tag and the density are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a l r : ℕ}

set_option maxHeartbeats 3600000 in
theorem ordered_first_two_volume_exchange
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    {U W : DefSet (M := M) (C.base : Set M) (n+2) a}
    {V : DefSet (M := M) (C.base : Set M) 0 l} {Z : DefSet (M := M) (C.base : Set M) 0 r}
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    (hfinW : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier W}.Finite)
    (δ : Fin a) (hδU : ∀ q : U, (q.val.2 δ).val ≠ iRVZero)
    (hδW : ∀ q : W, (q.val.2 δ).val ≠ iRVZero)
    (hSource : ∀ x : Fin n → VF (M := M), vfPrefixFibre (p := 2) W x =
      vfPermutationImage (vfPrefixFibre (p := 2) U x) swapTwo)
    (P : OrderedContractionProgram (C.base : Set M) U V)
    (Q : OrderedContractionProgram (C.base : Set M) W Z)
    (hP : GammaProgramDefinable B P) (hQ : GammaProgramDefinable B Q) :
    (gammaSelectedVolumeSchema V (gamma_program_final_set P hP) P.volumeIndex
      (suffixIndex P.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema Z (gamma_program_final_set Q hQ) (Q.volumeIndex ∘ swapFirstTwo n)
        (suffixIndex Q.rvArity_le δ)) (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  have hreal := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  cases P with
  | step T tail =>
    cases tail with
    | step T₂ tail₂ =>
      cases Q with
      | step E etail =>
        cases etail with
        | step E₂ etail₂ =>
          let PT := twoHeadPartialProgram T T₂
          let PE := twoHeadPartialProgram E E₂
          have hPT : GammaPartialProgramDefinable B PT :=
            ⟨hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,gamma_headImage T₂.target hP.2.2.2.1⟩
          have hPE : GammaPartialProgramDefinable B PE :=
            ⟨hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2.1,gamma_headImage E₂.target hQ.2.2.2.1⟩
          have hfinPE : ∀ (x : Fin n → VF (M := M)) (t : Fin 2 → RV (M := M)),
              {s | (x,s) ∈ carrier E₂.contractedSet ∧ s ∘ (PE.volumeIndex ∘ swapTwo.symm) = t}.Finite := by
            intro x t
            apply (partial_volume_fibres_finite C.uncountable.le C.saturated hreal PE hPE hfinW x (t ∘ swapTwo)).subset
            rintro s ⟨hs,ht⟩
            refine ⟨hs,funext (fun i => ?_)⟩
            have hi := congrFun ht (swapTwo i)
            simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hi
          have hGeom := lemma_7_5_ordered_geometric_at_generic (k := 1) hc C C.uncountable.le
            C.saturated C.model00 hreal hgamma γ hγ hγ1 hBC
            T₂.contractedSet E₂.contractedSet (gamma_partial_program_final_set PT hPT)
            (gamma_partial_program_final_set PE hPE) PT.volumeIndex (PE.volumeIndex ∘ swapTwo.symm)
            (suffixIndex PT.rvArity_le δ) (suffixIndex PE.rvArity_le δ)
            (fun q hq => partial_retained_density_nonzero PT δ hδU ⟨q,hq⟩)
            (fun q hq => partial_retained_density_nonzero PE δ hδW ⟨q,hq⟩)
            (partial_volume_fibres_finite C.uncountable.le C.saturated hreal PT hPT hfinU) hfinPE
            (fun x hx => two_partial_volume_rows_at_generic hc C hBC hNames hgamma hGenerated γ hγ hγ1
              hGeneric hU hfinU δ hδU hδW PT PE hPT hPE x hx swapTwo (hSource x))
            tail₂ etail₂ hP.2.2.2.2 hQ.2.2.2.2 (Fin.elim0 : Fin 0 → VF (M := M))
          have hδV := ordered_append_retained_density_nonzero tail₂ (suffixIndex PT.rvArity_le δ)
            (fun q hq => partial_retained_density_nonzero PT δ hδU ⟨q,hq⟩)
          have hδZ := ordered_append_retained_density_nonzero etail₂ (suffixIndex PE.rvArity_le δ)
            (fun q hq => partial_retained_density_nonzero PE δ hδW ⟨q,hq⟩)
          have h := selected_volume_geometry_reindex (two_head_tail_volume_degree n) V Z
            (gamma_program_final_set tail₂ hP.2.2.2.2) (gamma_program_final_set etail₂ hQ.2.2.2.2)
            (orderedAppendVolumeIndex tail₂ PT.volumeIndex)
            (orderedAppendVolumeIndex etail₂ (PE.volumeIndex ∘ swapTwo.symm))
            (OrderedContractionProgram.step T (.step T₂ tail₂)).volumeIndex
            ((OrderedContractionProgram.step E (.step E₂ etail₂)).volumeIndex ∘ swapFirstTwo n)
            (funext (two_head_tail_append_volume_index T T₂ tail₂))
            (funext (two_head_tail_append_swapped_volume_index E E₂ etail₂))
            _ _ hδV hδZ Fin.elim0 hGeom
          simpa only [PT,PE,two_head_tail_append_density_index] using h

end IntegrationInACVF.Section7
