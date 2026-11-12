import IntegrationSection6.GammaRVFamilyCodes
import IntegrationSection6.RVFamilyCodePairing

/-! One real-base RV code controls finitely many full Gamma RV families
at once, even when their RV arities differ. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gamma_rv_finite_families_code (FBase : VFFieldBase B.real) :
    ∀ (k : ℕ) (a : Fin k → ℕ)
      (r : ∀ i, Point (M := M) n 0 → Point (M := M) 0 (a i) → Prop),
      (∀ i, GammaGraphDefinable B (r i)) →
    ∃ d : ℕ, ∃ g : Map (PresentedSet.univ (pointSpace (M := M) n 0) B.real)
        (PresentedSet.univ (pointSpace (M := M) 0 d) B.real),
      GammaGraphDefinable B (pointMapGraph g) ∧
      ∀ x y, g x = g y → ∀ i z, r i x.val z ↔ r i y.val z := by
  let A := @PresentedSet.univ M sM (@pointSpace M sM hM n 0) B.real
  intro k
  induction k with
  | zero =>
    intro a r hr
    let g := constantRVMap (M := M) (sM := sM) (hM := hM) A 0
    refine ⟨0,g,(gammaLogicInput B).real_map_graph g,?_⟩
    intro x y h i
    exact i.elim0
  | succ k ih =>
    intro a r hr
    obtain ⟨d₀,g₀,hg₀,h₀⟩ := gamma_rv_family_finite_code FBase (r 0) (hr 0)
    obtain ⟨d₁,g₁,hg₁,h₁⟩ := ih (fun j => a j.succ) (fun j => r j.succ) (fun j => hr j.succ)
    let g := pairRVMaps (M := M) (sM := sM) (hM := hM) g₀ g₁
    refine ⟨d₀+d₁,g,(gammaLogicInput B).real_map_graph g,?_⟩
    intro x y h i
    cases i using Fin.cases with
    | zero => exact h₀ x y (pairRVMaps_eq_left g₀ g₁ h)
    | succ j => exact h₁ x y (pairRVMaps_eq_right g₀ g₁ h) j

end IntegrationInACVF.Section6
