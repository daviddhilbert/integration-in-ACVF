import Integration7.HeadCoordinateFibreVolumeSelectors
import IntegrationSection6.GammaHeadSelectedFiniteness

/-! Retain the old selected coordinates first and append the new head RV
tag. This order supports induction while keeping all density labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

def headAppendVolumeIndex (T : HeadPreparation U) (ρ : Fin (k+1) → Fin a) :
    Fin ((k+1)+1) → Fin (1+T.arity) :=
  Fin.append (headSelectedLabelIndex T ρ) (fun j : Fin 1 => Fin.castAdd T.arity j)

theorem head_append_selected_fibres_finite {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin ((k+1)+1) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) |
        (x,r) ∈ carrier T.contractedSet ∧ r ∘ headAppendVolumeIndex T ρ = t}.Finite := by
  intro x t
  apply (head_selected_fibres_finite hκ hs hreal T hT hTarget ρ hfin x
    (t ∘ (@finAddFlip 1 (k+1)))).subset
  rintro r ⟨hr,ht⟩
  refine ⟨hr,?_⟩
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [Function.comp_apply,headAppendVolumeIndex,headVolumeIndex,
      Fin.append_left,Fin.append_right,finAddFlip_apply_castAdd] using congrFun ht (Fin.natAdd (k+1) i)
  · simpa only [Function.comp_apply,headAppendVolumeIndex,headVolumeIndex,
      Fin.append_left,Fin.append_right,finAddFlip_apply_natAdd] using congrFun ht (Fin.castAdd 1 i)

theorem head_retained_density_nonzero
    (T : HeadPreparation U) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero) :
    ∀ p ∈ carrier T.contractedSet,
      (p.2 (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).val ≠ iRVZero := by
  intro p hp
  obtain ⟨u,hu⟩ := T.contractionMap_surjective ⟨p,hp⟩
  have hold : (T.contractionMap u).val.2
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) = u.val.2 δ := by
    change (headKeyMap T.target (T.map u)).val.2 _ = _
    rw [headKeyMap_apply]
    simpa only [headKey,Fin.append_right] using specialRelative_oldLabels T.special u δ
  rw [hu] at hold
  exact fun hz => hδ u.val u.property ((congrArg Subtype.val hold).symm.trans hz)

end IntegrationInACVF.Section7
