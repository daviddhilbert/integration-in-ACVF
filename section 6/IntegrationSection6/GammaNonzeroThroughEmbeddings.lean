import IntegrationSection6.GammaFiniteWeightAssembly
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

def gammaNonzeroGradedEvalAt (i : ℕ) : GammaNonzeroGradedAt (B := B) (S := S) →+
    GammaNonzeroClassesAt (B := B) (S := S) i where
  toFun a := a i
  map_zero' := rfl
  map_add' _ _ := rfl

def gammaThroughToGradedAt : ∀ k, GammaNonzeroThroughAt (B := B) (S := S) k →+ GammaNonzeroGradedAt (B := B) (S := S)
  | 0 => DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 0
  | n+1 => (gammaThroughToGradedAt n).coprod (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1))

def gammaGradedToThroughAt : ∀ k, GammaNonzeroGradedAt (B := B) (S := S) →+ GammaNonzeroThroughAt (B := B) (S := S) k
  | 0 => gammaNonzeroGradedEvalAt 0
  | n+1 => (gammaGradedToThroughAt n).prod (gammaNonzeroGradedEvalAt (n+1))

theorem gammaThroughToGradedAt_outside (k : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k) (i : ℕ) (hi : k < i) :
    gammaThroughToGradedAt k a i = 0 := by
  induction k with
  | zero => exact DirectSum.of_eq_of_ne (β := GammaNonzeroClassesAt (B := B) (S := S)) 0 i a (Nat.ne_of_gt hi)
  | succ n ih =>
    change gammaThroughToGradedAt n a.1 i + (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a.2) i = 0
    rw [ih a.1 (by omega),DirectSum.of_eq_of_ne _ _ _ (Nat.ne_of_gt hi),zero_add]

theorem gammaGradedToThroughAt_of_above (k j : ℕ) (x : GammaNonzeroClassesAt (B := B) (S := S) j) (hj : k < j) :
    gammaGradedToThroughAt k (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) j x) = 0 := by
  induction k with
  | zero => exact DirectSum.of_eq_of_ne j 0 x (Nat.ne_of_lt hj)
  | succ n ih =>
    apply Prod.ext
    · exact ih (by omega)
    · exact DirectSum.of_eq_of_ne j (n+1) x (Nat.ne_of_lt hj)

theorem gammaGradedToThroughAt_embed (k : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k) :
    gammaGradedToThroughAt k (gammaThroughToGradedAt k a) = a := by
  induction k with
  | zero => exact DirectSum.of_eq_same (β := GammaNonzeroClassesAt (B := B) (S := S)) 0 a
  | succ n ih =>
    apply Prod.ext
    · change gammaGradedToThroughAt n (gammaThroughToGradedAt n a.1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a.2) = a.1
      rw [map_add,ih,gammaGradedToThroughAt_of_above n (n+1) a.2 (Nat.lt_succ_self n),add_zero]
    · change gammaThroughToGradedAt n a.1 (n+1) + (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a.2) (n+1) = a.2
      rw [gammaThroughToGradedAt_outside n a.1 (n+1) (Nat.lt_succ_self n),DirectSum.of_eq_same,zero_add]

theorem gammaThroughToGradedAt_project_low (k : ℕ) (a : GammaNonzeroGradedAt (B := B) (S := S)) (i : ℕ) (hi : i ≤ k) :
    gammaThroughToGradedAt k (gammaGradedToThroughAt k a) i = a i := by
  induction k with
  | zero =>
    have he : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    exact DirectSum.of_eq_same 0 (a 0)
  | succ n ih =>
    change gammaThroughToGradedAt n (gammaGradedToThroughAt n a) i + (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) (a (n+1))) i = a i
    by_cases he : i = n+1
    · subst i
      rw [gammaThroughToGradedAt_outside n _ (n+1) (Nat.lt_succ_self n),DirectSum.of_eq_same,zero_add]
    · rw [ih (by omega),DirectSum.of_eq_of_ne _ _ _ he,add_zero]

theorem gammaThroughToGradedAt_project (k : ℕ) (a : GammaNonzeroGradedAt (B := B) (S := S))
    (h : ∀ i, k < i → a i = 0) : gammaThroughToGradedAt k (gammaGradedToThroughAt k a) = a := by
  apply DFinsupp.ext
  intro i
  by_cases hi : i ≤ k
  · exact gammaThroughToGradedAt_project_low k a i hi
  · rw [gammaThroughToGradedAt_outside k _ i (by omega),h i (by omega)]

theorem gammaThroughToGradedAt_injective (k : ℕ) : Function.Injective (gammaThroughToGradedAt (B := B) (S := S) k) :=
  Function.LeftInverse.injective (gammaGradedToThroughAt_embed k)

end IntegrationInACVF.Section6.FiniteRV
