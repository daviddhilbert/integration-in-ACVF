import Integration7.RVLabelCutMaps
import IntegrationSection6.GammaHeadFibreLiftMaps

/-! Actual head preparations restrict to arbitrary original-Gamma
old-label predicates. The head tag and all passive VF coordinates remain
available for the following contraction steps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

def cutHeadOldLabelIndex (T : HeadPreparation U) (ρ : Fin k → Fin a) : Fin k → Fin T.arity :=
  suffixIndex (specialRelative_rvArity_le T.special) ∘ ρ

theorem cut_head_old_labels (T : HeadPreparation U) (ρ : Fin k → Fin a) (u : U) :
    (T.map u).val.2 ∘ cutHeadOldLabelIndex T ρ = u.val.2 ∘ ρ :=
  funext (fun j => specialRelative_oldLabels T.special u (ρ j))

def rvLabelCutHeadPreparation (T : HeadPreparation U) (hU : GammaSetDefinable G (carrier U))
    (hTarget : GammaSetDefinable G (carrier T.target)) (ρ : Fin k → Fin a)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    HeadPreparation (rvLabelCut U hU ρ R hR hNames) where
  arity := T.arity
  target := rvLabelCut T.target hTarget (cutHeadOldLabelIndex T ρ) R hR hNames
  map := rvLabelCutMap T.map T.bijective hU hTarget ρ (cutHeadOldLabelIndex T ρ) (cut_head_old_labels T ρ) R hR hNames
  special := special_relative_rv_label_cut_map T.map T.bijective hU hTarget ρ (cutHeadOldLabelIndex T ρ)
    (cut_head_old_labels T ρ) R hR hNames T.special
  saturated := fun q hq z hz => ⟨T.saturated q hq.1 z hz,hq.2⟩

theorem rv_label_cut_head_preparation_contracted (T : HeadPreparation U) (hU : GammaSetDefinable G (carrier U))
    (hTarget : GammaSetDefinable G (carrier T.target)) (ρ : Fin k → Fin a)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    (rvLabelCutHeadPreparation T hU hTarget ρ R hR hNames).contractedSet =
      rvLabelCut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ρ) R hR hNames :=
  rv_label_cut_head_image hTarget (cutHeadOldLabelIndex T ρ) R hR hNames

theorem gamma_rv_label_cut_head_preparation_map (T : HeadPreparation U) (hU : GammaSetDefinable G (carrier U))
    (hT : GammaGraphDefinable G (pointMapGraph T.map))
    (hTarget : GammaSetDefinable G (carrier T.target)) (ρ : Fin k → Fin a)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    GammaGraphDefinable G (pointMapGraph (rvLabelCutHeadPreparation T hU hTarget ρ R hR hNames).map) :=
  gamma_rv_label_cut_map T.map T.bijective hU hTarget ρ (cutHeadOldLabelIndex T ρ)
    (cut_head_old_labels T ρ) R hR hNames hT

theorem gamma_rv_label_cut_head_preparation_target (T : HeadPreparation U) (hU : GammaSetDefinable G (carrier U))
    (hTarget : GammaSetDefinable G (carrier T.target)) (ρ : Fin k → Fin a)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    GammaSetDefinable G (carrier (rvLabelCutHeadPreparation T hU hTarget ρ R hR hNames).target) :=
  gamma_rv_label_cut T.target hTarget (cutHeadOldLabelIndex T ρ) R hR

end IntegrationInACVF.Section7
