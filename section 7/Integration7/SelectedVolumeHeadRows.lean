import Integration7.GammaSelectedVolumeSchemata
import Integration7.GammaGeometricCommonRowTransport
import IntegrationSection6.GammaHeadFibreParameters

/-! Freezing the VF tail retains literally the selected coordinate and
density rows and exactly the same mathematical parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a k : ℕ}

theorem selected_volume_head_coordinate_rows
    (U : DefSet (M := M) S (n+1) a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M))
    (r : Fin a → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).object.rowVolume
        (fun j => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).val) r y ↔
      (gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x))
        (gamma_head_fibre U hU x) ρ δ).object.rowVolume (fun j => (z j).val) r y := by
  refine (gammaSelectedLabelSchema_volume U hU ρ (Fin.cons (z 0) x) r y).trans (Iff.trans ?_
    (gammaSelectedLabelSchema_volume (coordinateFibre U 0 (headFrozenTuple x))
      (gamma_head_fibre U hU x) ρ z r y).symm)
  change ((_ ∈ carrier U) ∧ _) ↔ ((coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier U) ∧ _)
  rw [coordinateInsert_head]
  rfl

theorem selected_volume_head_density_rows
    (U : DefSet (M := M) S (n+1) a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hNZ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M))
    (r : Fin a → RV (M := M)) (w : Fin 1 → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).rowDensity (fun j => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).val) r w ↔
      (gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x))
        (gamma_head_fibre U hU x) ρ δ).rowDensity (fun j => (z j).val) r w := by
  have hNZ' : ∀ p ∈ carrier (coordinateFibre U 0 (headFrozenTuple x)), (p.2 δ).val ≠ iRVZero :=
    fun p hp => hNZ (coordinateInsert 0 (headFrozenTuple x) p) hp
  rw [gammaSelectedVolumeSchema_density U hU ρ δ hNZ,
    gammaSelectedVolumeSchema_density _ (gamma_head_fibre U hU x) ρ δ hNZ']
  change ((_ ∈ carrier U) ∧ _) ↔ ((coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier U) ∧ _)
  rw [coordinateInsert_head]
  rfl

end IntegrationInACVF.Section7
