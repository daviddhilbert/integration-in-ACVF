import Integration7.VolumeCoordinateChartInverses

/-! Reverse the common coordinate-order conversion on two specified
integral contraction objects. The unchanged densities are compared on
both sides together, so no unsigned permutation isomorphism is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_appended_common_of_canonical
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (B : DefSet (M := M) (C.base : Set M) (n+1) b)
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier B, (p.2 ε).val ≠ iRVZero)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinB : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier B ∧ r ∘ τ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) (E : StandardContraction B (Equiv.refl _))
    (h : VolumeBlowupEquivalent (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfinA T)
      (selectedStandardVolumeObject hc C Ξ B τ ε hε hfinB E)) :
    VolumeBlowupEquivalent (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfinA T)
      (standardAppendVolumeObject hc C Ξ B τ ε hε hfinB E) := by
  let fA := selectedIntegralCoordinateChart hc C Ξ A ρ δ hδ hfinA T
  let fB := selectedIntegralCoordinateChart hc C Ξ B τ ε hε hfinB E
  exact (h.reindexDegree hc C (selected_append_degree_eq n k)).of_permuted_coordinate_charts hc C
    (appendedToOriginalVolumePermutation (n+1) k).symm fA.symm fB.symm
    (finite_volume_coordinate_chart_inverse fA _ (selected_integral_coordinate_chart_coordinates hc C Ξ A ρ δ hδ hfinA T))
    (finite_volume_coordinate_chart_inverse fB _ (selected_integral_coordinate_chart_coordinates hc C Ξ B τ ε hε hfinB E))
    (finite_volume_density_chart_inverse fA (selected_integral_coordinate_chart_density hc C Ξ A ρ δ hδ hfinA T))
    (finite_volume_density_chart_inverse fB (selected_integral_coordinate_chart_density hc C Ξ B τ ε hε hfinB E))

end IntegrationInACVF.Section7
