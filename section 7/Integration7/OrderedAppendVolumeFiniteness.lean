import Integration7.OrderedAppendVolumeContractions
import Integration7.OrderedAppendVolumeIndices

/-! Actual finiteness and density nonvanishing for the complete appended
coordinate tuple of any chosen contraction program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}

theorem ordered_append_volume_fibres_finite {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) :
    ∀ {n a l k : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
      (T : OrderedContractionProgram S U V) (hT : GammaProgramDefinable B T)
      (ρ : Fin (k+1) → Fin a),
      (∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
        {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) →
      ∀ t : Fin (appendVolumeDegree n k + 1) → RV (M := M),
        {r : Fin l → RV (M := M) | (Fin.elim0,r) ∈ carrier V ∧ r ∘ orderedAppendVolumeIndex T ρ = t}.Finite := by
  intro n
  induction n with
  | zero =>
    intro a l k U V T hT ρ hfin t
    cases T
    exact hfin Fin.elim0 t
  | succ n ih =>
    intro a l k U V T hT ρ hfin t
    cases T with
    | step T tail =>
      exact ih tail hT.2.2 (headAppendVolumeIndex T ρ)
        (head_append_selected_fibres_finite hκ hs hreal T hT.1 hT.2.1 ρ hfin) t

theorem ordered_append_retained_density_nonzero
    {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) :
    ∀ q ∈ carrier V, (q.2 (orderedAppendDensityIndex T δ)).val ≠ iRVZero := by
  intro q hq
  obtain ⟨p,hp⟩ := T.surjective ⟨q,hq⟩
  have hOld := T.oldLabels p δ
  rw [hp] at hOld
  rw [ordered_append_density_index, hOld]
  exact hδ p.val p.property

end IntegrationInACVF.Section7
