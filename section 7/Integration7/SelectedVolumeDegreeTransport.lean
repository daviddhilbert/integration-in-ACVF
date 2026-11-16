module

public import Integration7.GeometricVolumeDegreeTransports
public import Integration7.GammaSelectedVolumeSchemata

@[expose] public section

/-! Reindex a full selected volume schema along its actual degree and
selector equality, retaining every label and the original density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b j k : ℕ}

private theorem selected_eq_reindex_iff {r : ℕ} (h : j=k)
    (ρ : Fin (j+1) → Fin r) (ρ' : Fin (k+1) → Fin r)
    (hρ : ρ ∘ (finCongr (congrArg Nat.succ h)).symm = ρ')
    (x : Fin r → RV (M := M)) (y : Fin (k+1) → RV (M := M)) :
    x ∘ ρ = y ∘ (finCongr (congrArg Nat.succ h)) ↔ x ∘ ρ' = y := by
  let e := finCongr (congrArg Nat.succ h)
  constructor
  · intro he
    funext i
    have hi := congrFun he (e.symm i)
    change x (ρ (e.symm i)) = y (e (e.symm i)) at hi
    rw [e.apply_symm_apply] at hi
    exact (congrArg x (congrFun hρ i)).symm.trans hi
  · intro he
    funext i
    have hi := congrFun he (e i)
    change x (ρ' (e i)) = y (e i) at hi
    have hIndex := congrFun hρ (e i)
    change ρ (e.symm (e i)) = ρ' (e i) at hIndex
    rw [e.symm_apply_apply] at hIndex
    exact (congrArg x hIndex).trans hi

theorem selected_volume_geometry_reindex (h : j=k)
    (U : DefSet (M := M) S p a) (V : DefSet (M := M) S p b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (j+1) → Fin a) (τ : Fin (j+1) → Fin b)
    (ρ' : Fin (k+1) → Fin a) (τ' : Fin (k+1) → Fin b)
    (hρ : ρ ∘ (finCongr (congrArg Nat.succ h)).symm = ρ')
    (hτ : τ ∘ (finCongr (congrArg Nat.succ h)).symm = τ')
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (hε : ∀ q ∈ carrier V, (q.2 ε).val ≠ iRVZero)
    (x : Fin p → VF (M := M))
    (hGeom : (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema V hV τ ε) (fun i => (x i).val)) :
    (gammaSelectedVolumeSchema U hU ρ' δ).commonByGammaGeometry
      (gammaSelectedVolumeSchema V hV τ' ε) (fun i => (x i).val) := by
  apply GammaRVVolumeSchema.commonByGammaGeometry_transport_degree h _ _ _ _ _ ?_ ?_ ?_ ?_ hGeom
  · intro r y
    exact (gammaSelectedLabelSchema_volume U hU ρ x r _).trans
      ((and_congr_right (fun _ => selected_eq_reindex_iff h ρ ρ' hρ r y)).trans
        (gammaSelectedLabelSchema_volume U hU ρ' x r y).symm)
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ hδ,gammaSelectedVolumeSchema_density _ _ _ _ hδ]
  · intro r y
    exact (gammaSelectedLabelSchema_volume V hV τ x r _).trans
      ((and_congr_right (fun _ => selected_eq_reindex_iff h τ τ' hτ r y)).trans
        (gammaSelectedLabelSchema_volume V hV τ' x r y).symm)
  · intro r w
    rw [gammaSelectedVolumeSchema_density _ _ _ _ hε,gammaSelectedVolumeSchema_density _ _ _ _ hε]

end IntegrationInACVF.Section7
