import IntegrationSection6.OrderedSelectedVolume
import IntegrationSection5.GammaPartialContraction

/-! The selected-coordinate volume of a partial contraction retains every
contracted head RV value and all originally selected labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a l : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}

def partialSelectedIndex (T : PartialContractionProgram S n (n := p) U V) {k : ℕ} (ρ : Fin k → Fin a) :
    Fin (orderedVolumeDegree p k) → Fin l := by
  induction T generalizing k with
  | zero U => exact ρ
  | step T tail ih => exact ih (headVolumeIndex T ρ)

theorem partial_selected_fibres_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (T : PartialContractionProgram S n (n := p) U V) (hT : GammaPartialProgramDefinable B T)
    {k : ℕ} (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin (n+p) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin (orderedVolumeDegree p k) → RV (M := M)),
      {r : Fin l → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ partialSelectedIndex T ρ = t}.Finite := by
  induction T generalizing k with
  | zero U => exact hfin
  | step T tail ih =>
    exact ih hT.2.2 (headVolumeIndex T ρ)
      (head_selected_fibres_finite hκ hs hreal T hT.1 hT.2.1 ρ hfin)

end IntegrationInACVF.Section6
