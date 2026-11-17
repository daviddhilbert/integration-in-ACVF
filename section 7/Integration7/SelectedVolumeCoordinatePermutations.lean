module

public import Integration7.GammaPermutedVolumeSchemaRows
public import Integration7.GammaSelectedVolumeSchemata

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A common coordinate permutation of selected volume rows retains
their geometric comparison and unchanged full retained densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

private theorem coordinate_eq_permute_iff {r : ℕ} (ρ : Fin (k+1) → Fin r)
    (e : Equiv.Perm (Fin (k+1))) (x : Fin r → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    x ∘ (ρ ∘ e) = y ↔ x ∘ ρ = y ∘ e.symm := by
  constructor
  · intro h
    funext i
    have hi := congrFun h (e.symm i)
    simpa only [Function.comp_apply,e.apply_symm_apply] using hi
  · intro h
    funext i
    have hi := congrFun h (e i)
    simpa only [Function.comp_apply,e.symm_apply_apply] using hi

theorem selected_volume_geometry_permute
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S p a) (V : DefSet (M := M) S p b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (hε : ∀ q ∈ carrier V, (q.2 ε).val ≠ iRVZero)
    (x : Fin p → VF (M := M)) (e : Equiv.Perm (Fin (k+1)))
    (hGeom : (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema V hV τ ε) (fun i => (x i).val)) :
    (gammaSelectedVolumeSchema U hU (ρ ∘ e) δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema V hV (τ ∘ e) ε) (fun i => (x i).val) := by
  apply GammaRVVolumeSchema.commonByGammaGeometry_permute_volume hc _ _ _ _ _ e ?_ ?_ ?_ ?_ hGeom
  · intro r y
    exact (gammaSelectedLabelSchema_volume U hU (ρ ∘ e) x r y).trans
      ((and_congr_right (fun _ => coordinate_eq_permute_iff ρ e r y)).trans
        (gammaSelectedLabelSchema_volume U hU ρ x r (y ∘ e.symm)).symm)
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ hδ,gammaSelectedVolumeSchema_density _ _ _ _ hδ]
  · intro r y
    exact (gammaSelectedLabelSchema_volume V hV (τ ∘ e) x r y).trans
      ((and_congr_right (fun _ => coordinate_eq_permute_iff τ e r y)).trans
        (gammaSelectedLabelSchema_volume V hV τ x r (y ∘ e.symm)).symm)
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ hε,gammaSelectedVolumeSchema_density _ _ _ _ hε]

end IntegrationInACVF.Section7
