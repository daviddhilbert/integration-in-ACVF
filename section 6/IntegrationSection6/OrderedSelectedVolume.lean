import IntegrationSection6.GammaHeadSelectedFiniteness

/-! The actual selected volume retained by an ordered contraction. Its
recursive order lists the contracted VF labels backwards, then the old
selected labels. The number of volume coordinates is n+k. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}

def orderedVolumeDegree : ℕ → ℕ → ℕ
  | 0,k => k
  | n+1,k => orderedVolumeDegree n (1+k)

theorem orderedVolumeDegree_eq (n k : ℕ) : orderedVolumeDegree n k = n+k := by
  induction n generalizing k with
  | zero => simp [orderedVolumeDegree]
  | succ n ih => rw [orderedVolumeDegree,ih]; omega

def orderedSelectedIndex {n m l : ℕ} {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) {k : ℕ} (ρ : Fin k → Fin m) :
    Fin (orderedVolumeDegree n k) → Fin l := by
  induction T generalizing k with
  | zero A => exact ρ
  | step T tail ih => exact ih (headVolumeIndex T ρ)

theorem ordered_selected_fibres_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    {n m l : ℕ} {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) (hT : GammaProgramDefinable B T)
    {k : ℕ} (ρ : Fin k → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite) :
    ∀ t : Fin (orderedVolumeDegree n k) → RV (M := M),
      {r : Fin l → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ orderedSelectedIndex T ρ = t}.Finite := by
  induction T generalizing k with
  | zero A => exact hfin Fin.elim0
  | step T tail ih =>
    exact ih hT.2.2 (headVolumeIndex T ρ)
      (head_selected_fibres_finite hκ hs hreal T hT.1 hT.2.1 ρ hfin)

end IntegrationInACVF.Section6
