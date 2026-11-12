import IntegrationSection6.RVLabelSliceMaps
import IntegrationSection6.GammaHeadFibreLiftMaps

/-! Head preparations restrict to fixed old RV labels. The new head RV
value is free, and the selected old labels remain a known suffix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a}

def headTargetOldLabelIndex (T : HeadPreparation U) (ρ : Fin k → Fin a) : Fin k → Fin T.arity :=
  fun j => suffixIndex (specialRelative_rvArity_le T.special) (ρ j)

theorem headTargetOldLabels (T : HeadPreparation U) (ρ : Fin k → Fin a) (u : U) :
    (T.map u).val.2 ∘ headTargetOldLabelIndex T ρ = u.val.2 ∘ ρ := by
  funext j
  exact specialRelative_oldLabels T.special u (ρ j)

def rvLabelHeadPreparation (T : HeadPreparation U) (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    HeadPreparation (rvLabelSlice U hU ρ t) where
  arity := T.arity
  target := rvLabelSlice T.target hTarget (headTargetOldLabelIndex T ρ) t
  map := rvLabelSliceMap T.map T.bijective hU hTarget ρ (headTargetOldLabelIndex T ρ) (headTargetOldLabels T ρ) t
  special := specialRelative_rvLabelSliceMap T.map T.bijective hU hTarget ρ (headTargetOldLabelIndex T ρ)
    (headTargetOldLabels T ρ) t T.special
  saturated := by
    intro q hq z hz
    exact ⟨T.saturated q hq.1 z hz,hq.2⟩

theorem rvLabelHeadPreparation_contracted (T : HeadPreparation U) (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    (rvLabelHeadPreparation T hU hTarget ρ t).contractedSet =
      rvLabelSlice T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ρ) t :=
  rvLabelSlice_headImage T.target hTarget (headTargetOldLabelIndex T ρ) t

theorem gamma_rvLabelHeadPreparation_map (T : HeadPreparation U) (hU : GammaSetDefinable B (carrier U))
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hTarget : GammaSetDefinable B (carrier T.target))
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (pointMapGraph (rvLabelHeadPreparation T hU hTarget ρ t).map) :=
  gamma_rvLabelSliceMap T.map T.bijective hU hTarget ρ (headTargetOldLabelIndex T ρ) (headTargetOldLabels T ρ) t hT

theorem gamma_rvLabelHeadPreparation_target (T : HeadPreparation U) (hU : GammaSetDefinable B (carrier U))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (carrier (rvLabelHeadPreparation T hU hTarget ρ t).target) :=
  rvLabelSlice_gamma T.target hTarget (headTargetOldLabelIndex T ρ) t

end IntegrationInACVF.Section6
