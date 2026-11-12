import IntegrationSection6.GammaNonzeroThroughEmbeddings
import IntegrationSection6.GammaPaddingClasses
import IntegrationSection6.GammaNonzeroGradedSemiring
import IntegrationSection6.GammaFiniteRestrictionIsomorphisms
import IntegrationSection6.FiniteGammaLocusBlowups
import IntegrationSection6.GammaWeightStrata
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual original-Gamma RV[k] isomorphism
classes. This follows the pinned RVHomogeneousProducts/RVGradedSemiring
construction, using the finite Gamma structural maps proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

variable [hBS : Fact (B.real ⊆ S)]

theorem gammaNonzeroGraded_bounded (a : GammaNonzeroGradedAt (B := B) (S := S)) :
    ∃ k, ∀ i, k < i → a i = 0 := by
  obtain ⟨k,hk⟩ := (DFinsupp.finite_support a).bddAbove
  refine ⟨k,fun i hi => ?_⟩
  by_contra hn
  exact (not_le_of_gt hi) (hk hn)

theorem gammaThroughToGradedAt_exhaustive (a : GammaNonzeroGradedAt (B := B) (S := S)) :
    ∃ k, ∃ x : GammaNonzeroThroughAt (B := B) (S := S) k, gammaThroughToGradedAt k x = a := by
  obtain ⟨k,hk⟩ := gammaNonzeroGraded_bounded a
  exact ⟨k,gammaGradedToThroughAt k a,gammaThroughToGradedAt_project k a hk⟩

theorem gammaThroughToGradedAt_inclusion (n : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) n) :
    gammaThroughToGradedAt (n+1) (gammaNonzeroThroughInclusionAt n a) = gammaThroughToGradedAt n a := by
  change gammaThroughToGradedAt n a + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) 0 = _
  rw [map_zero,add_zero]

def gammaThroughTransitionAt {i j : ℕ} (hij : i ≤ j) :
    GammaNonzeroThroughAt (B := B) (S := S) i →+ GammaNonzeroThroughAt (B := B) (S := S) j :=
  (gammaGradedToThroughAt j).comp (gammaThroughToGradedAt i)

theorem gammaThroughTransitionAt_embed {i j : ℕ} (hij : i ≤ j) (a : GammaNonzeroThroughAt (B := B) (S := S) i) :
    gammaThroughToGradedAt j (gammaThroughTransitionAt hij a) = gammaThroughToGradedAt i a :=
  gammaThroughToGradedAt_project j _ (fun k hk => gammaThroughToGradedAt_outside i a k (by omega))

theorem gammaThroughTransitionAt_refl (i : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) i) :
    gammaThroughTransitionAt (le_refl i) a = a := gammaGradedToThroughAt_embed i a

theorem gammaThroughTransitionAt_trans {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l)
    (a : GammaNonzeroThroughAt (B := B) (S := S) i) :
    gammaThroughTransitionAt hjl (gammaThroughTransitionAt hij a) = gammaThroughTransitionAt (hij.trans hjl) a := by
  apply gammaThroughToGradedAt_injective l
  rw [gammaThroughTransitionAt_embed,gammaThroughTransitionAt_embed,gammaThroughTransitionAt_embed]

theorem gammaThroughTransitionAt_succ (n : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) n) :
    gammaThroughTransitionAt (Nat.le_succ n) a = gammaNonzeroThroughInclusionAt n a := by
  apply gammaThroughToGradedAt_injective (n+1)
  rw [gammaThroughTransitionAt_embed,gammaThroughToGradedAt_inclusion]

theorem gammaThroughTransitionAt_injective {i j : ℕ} (hij : i ≤ j) :
    Function.Injective (gammaThroughTransitionAt (B := B) (S := S) hij) := by
  intro a b he
  apply gammaThroughToGradedAt_injective i
  exact (gammaThroughTransitionAt_embed hij a).symm.trans
    ((congrArg (gammaThroughToGradedAt j) he).trans (gammaThroughTransitionAt_embed hij b))

end IntegrationInACVF.Section6.FiniteRV
