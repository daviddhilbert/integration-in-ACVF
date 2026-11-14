import Integration7.OrderedAppendVolumeContractions
import Integration7.GammaPermutedSelectedVolumeFamilies

/-! Positive selected-volume comparison for arbitrary chosen standard
contractions with the same VF-coordinate order. The contracted tags are
retained in that common order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b k : ℕ}

set_option maxHeartbeats 2400000 in
theorem lemma_7_5_standard_geometric {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) n a) (V : DefSet (M := M) (C.base : Set M) n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin a → RV (M := M) | (x,v) ∈ carrier U ∧ v ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin b → RV (M := M) | (x,v) ∈ carrier V ∧ v ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin n → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
        (orderedAppendVolumeIndex T.program ρ) (orderedAppendDensityIndex T.program δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE)
        (orderedAppendVolumeIndex E.program τ) (orderedAppendDensityIndex E.program ε)) (fun j => (x j).val) := by
  exact lemma_7_5_ordered_geometric hc C hκ hs h00 hreal hgamma γ hγ hγ1 hBC
    (vfPermutationImage U σ) (vfPermutationImage V σ) (gamma_vfPermutationImage U hU σ) (gamma_vfPermutationImage V hV σ)
    ρ τ δ ε (vf_permuted_retained_density_nonzero U σ δ hδ) (vf_permuted_retained_density_nonzero V σ ε hε)
    (vfPermutation_selected_finite U σ ρ hfinU) (vfPermutation_selected_finite V σ τ hfinV)
    (fun x => vf_permuted_selected_geometric_common U V hU hV σ ρ τ δ ε hδ hε hCommon x) T.program E.program hT hE

end IntegrationInACVF.Section7
