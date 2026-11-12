import IntegrationSection6.FiniteNonzeroIntegration
import IntegrationSection6.GammaNonzeroThroughTransitions
import IntegrationSection6.GammaIspPadding

/-! The nonzero-coordinate filtered form of fixed-degree integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

variable (hB : VFGammaGeneratedBase B)

include FBase hgamma δ hδ hδ1 h58 hB in
theorem gammaThroughIsp_transition_iff {i j : ℕ} (hij : i ≤ j)
    (a b : GammaNonzeroThroughAt (B := B) (S := Set.univ) i) :
    gammaNonzeroThroughIspAt hκ hs h00 hreal j (gammaThroughTransitionAt hij a) (gammaThroughTransitionAt hij b) ↔
      gammaNonzeroThroughIspAt hκ hs h00 hreal i a b := by
  induction j,hij using Nat.le_induction with
  | base => simp only [gammaThroughTransitionAt_refl]
  | succ j hij ih =>
    have he (x : GammaNonzeroThroughAt (B := B) (S := Set.univ) i) :
        gammaThroughTransitionAt (hij.trans (Nat.le_succ j)) x =
          gammaNonzeroThroughInclusionAt j (gammaThroughTransitionAt hij x) := by
      rw [← gammaThroughTransitionAt_trans hij (Nat.le_succ j),gammaThroughTransitionAt_succ]
    rw [he a,he b,gammaNonzeroThroughIspAt_compatible hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB]
    exact ih

end IntegrationInACVF.Section6.FiniteRV
