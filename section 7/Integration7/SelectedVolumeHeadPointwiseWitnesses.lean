module

public import Integration7.SelectedVolumeHeadRows
public import Integration7.SelectedVolumeSchemaUniformBounds

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The original fibrewise geometric hypothesis specializes to a unary
head fibre over exactly the frozen VF base, and gives full formula
witnesses for arbitrary auxiliary exception parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a b k : ℕ}

theorem selected_volume_head_geometric_common
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hCommon : ∀ x : Fin (n+1) → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    (x : Fin n → VF (M := M)) (z : Fin 1 → VF (M := M)) :
    (gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x)) (gamma_head_fibre U hU x) ρ δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema (coordinateFibre V 0 (headFrozenTuple x)) (gamma_head_fibre V hV x) τ ε)
      (fun j => (z j).val) := by
  exact GammaRVVolumeSchema.commonByGammaGeometry_transport_rows (headVFParameterBase x z).symm
    (selected_volume_head_coordinate_rows U hU ρ δ x z)
    (selected_volume_head_density_rows U hU ρ δ hδ x z)
    (selected_volume_head_coordinate_rows V hV τ ε x z)
    (selected_volume_head_density_rows V hV τ ε hε x z) (hCommon (Fin.cons (z 0) x))

theorem selected_volume_head_formula_witnesses {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U : DefSet (M := M) S (n+1) a) (V : DefSet (M := M) S (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hCommon : ∀ x : Fin (n+1) → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    (x : Fin n → VF (M := M)) (NF NG : ℕ)
    (hF : ∀ z : Fin 1 → VF (M := M),
      ((gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x))
        (gamma_head_fibre U hU x) ρ δ).withBound NF).valid (fun j => (z j).val))
    (hG : ∀ z : Fin 1 → VF (M := M),
      ((gammaSelectedVolumeSchema (coordinateFibre V 0 (headFrozenTuple x))
        (gamma_head_fibre V hV x) τ ε).withBound NG).valid (fun j => (z j).val)) :
    ∀ z : Fin 1 → VF (M := M), ∃ H : GammaVolumeCommonSchema
      ((gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x)) (gamma_head_fibre U hU x) ρ δ).withBound NF)
      ((gammaSelectedVolumeSchema (coordinateFibre V 0 (headFrozenTuple x)) (gamma_head_fibre V hV x) τ ε).withBound NG),
      H.valid (fun j => (z j).val) := by
  intro z
  apply gamma_volume_formula_witness_from_geometry
    (B := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩) hc hκ hs h00
    (small_union_range hκ B.real hreal (fun j => (x j).val)) hgamma _ _ _ (hF z) (hG z)
  exact GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
    (F := gammaSelectedVolumeSchema (coordinateFibre U 0 (headFrozenTuple x)) (gamma_head_fibre U hU x) ρ δ)
    (G := gammaSelectedVolumeSchema (coordinateFibre V 0 (headFrozenTuple x)) (gamma_head_fibre V hV x) τ ε) rfl
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (selected_volume_head_geometric_common U V hU hV ρ τ δ ε hδ hε hCommon x z)

end IntegrationInACVF.Section7
