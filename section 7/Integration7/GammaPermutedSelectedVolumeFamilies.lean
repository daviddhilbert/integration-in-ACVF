module

public import Integration7.GammaGeometricCommonRowTransport
public import Integration7.GammaSelectedVolumeSchemata
public import IntegrationSection6.GammaPermutedFibrePresentations

@[expose] public section

/-! The same VF-coordinate permutation on both families preserves the
ordinary selected coordinates, density labels and exact geometric bases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}

theorem vf_permuted_retained_density_nonzero
    (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n)) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) :
    ∀ p ∈ carrier (vfPermutationImage U σ), (p.2 δ).val ≠ iRVZero :=
  fun p hp => hδ (p.1 ∘ σ.symm,p.2) ((vfPermutationImage_row U σ p.1 p.2).mp hp)

theorem vf_permuted_selected_coordinate_rows
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U)) (σ : Equiv.Perm (Fin n))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a) (x : Fin n → VF (M := M))
    (r : Fin a → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).object.rowVolume (fun j => (x (σ.symm j)).val) r y ↔
      (gammaSelectedVolumeSchema (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ δ).object.rowVolume
        (fun j => (x j).val) r y := by
  exact (gammaSelectedLabelSchema_volume U hU ρ (x ∘ σ.symm) r y).trans
    ((and_congr (vfPermutationImage_row U σ x r).symm Iff.rfl).trans
      (gammaSelectedLabelSchema_volume (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ x r y).symm)

theorem vf_permuted_selected_density_rows
    (U : DefSet (M := M) S n a) (hU : GammaSetDefinable B (carrier U)) (σ : Equiv.Perm (Fin n))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a) (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (x : Fin n → VF (M := M)) (r : Fin a → RV (M := M)) (w : Fin 1 → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).rowDensity (fun j => (x (σ.symm j)).val) r w ↔
      (gammaSelectedVolumeSchema (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ δ).rowDensity
        (fun j => (x j).val) r w := by
  exact (gammaSelectedVolumeSchema_density U hU ρ δ hδ (x ∘ σ.symm) r w).trans
    ((and_congr (vfPermutationImage_row U σ x r).symm Iff.rfl).trans
      (gammaSelectedVolumeSchema_density (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ δ
        (vf_permuted_retained_density_nonzero U σ δ hδ) x r w).symm)

theorem vf_permuted_selected_geometric_common
    (U : DefSet (M := M) S n a) (V : DefSet (M := M) S n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (σ : Equiv.Perm (Fin n)) (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (h : ∀ x : Fin n → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val)) (x : Fin n → VF (M := M)) :
    (gammaSelectedVolumeSchema (vfPermutationImage U σ) (gamma_vfPermutationImage U hU σ) ρ δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema (vfPermutationImage V σ) (gamma_vfPermutationImage V hV σ) τ ε)
      (fun j => (x j).val) := by
  exact GammaRVVolumeSchema.commonByGammaGeometry_transport_rows (vfPermutationParameterBase σ x).symm
    (vf_permuted_selected_coordinate_rows U hU σ ρ δ x) (vf_permuted_selected_density_rows U hU σ ρ δ hδ x)
    (vf_permuted_selected_coordinate_rows V hV σ τ ε x) (vf_permuted_selected_density_rows V hV σ τ ε hε x)
    (h (x ∘ σ.symm))

end IntegrationInACVF.Section7
