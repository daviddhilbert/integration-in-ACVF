import IntegrationSection6.FiniteGammaInitial
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Actual original-Gamma RV[k] isomorphism classes, with coproduct addition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}

instance gammaAtCocartesianMonoidal [Fact (B.real ⊆ S)] : MonoidalCategory (GammaObjectAt B S n) :=
  monoidalOfHasFiniteCoproducts _

instance gammaAtCocartesianSymmetric [Fact (B.real ⊆ S)] : SymmetricCategory (GammaObjectAt B S n) :=
  symmetricOfHasFiniteCoproducts _

abbrev GammaIsoClassesAt (B : Base (M := M)) (S : Set M) (n : ℕ) := Additive (Skeleton (GammaObjectAt B S n))

def gammaIsoClassAt (U : GammaObjectAt B S n) : GammaIsoClassesAt B S n := Additive.ofMul (toSkeleton U)

theorem gammaIsoClassAt_eq_iff {U V : GammaObjectAt B S n} :
    gammaIsoClassAt U = gammaIsoClassAt V ↔ Nonempty (GammaIsoAt U V) :=
  toSkeleton_eq_toSkeleton_iff.trans (gammaIsoAt_iff_iso U V).symm

theorem gammaIsoClassAt_iso {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) :
    gammaIsoClassAt U = gammaIsoClassAt V := gammaIsoClassAt_eq_iff.mpr ⟨e⟩

@[simp] theorem gammaIsoClassAt_empty (hBS : B.real ⊆ S) [Fact (B.real ⊆ S)] :
    gammaIsoClassAt (gammaEmptyAt (n := n) hBS) = 0 := by
  change toSkeleton (gammaEmptyAt hBS) = (1 : Skeleton (GammaObjectAt B S n))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso ((gammaEmptyIsInitial hBS).uniqueUpToIso initialIsInitial)

theorem gammaIsoClassAt_coprod [Fact (B.real ⊆ S)] (U V : GammaObjectAt B S n) :
    gammaIsoClassAt (gammaCoprodAt U V) = gammaIsoClassAt U + gammaIsoClassAt V := by
  change toSkeleton (gammaCoprodAt U V) = toSkeleton U * toSkeleton V
  calc
    _ = toSkeleton (U ⨿ V) := congr_toSkeleton_of_iso
      (colimit.isoColimitCocone
        { cocone := BinaryCofan.mk (gammaCoprodInlAt U V) (gammaCoprodInrAt U V)
          isColimit := gammaCoprodIsColimit U V }).symm
    _ = _ := Skeleton.toSkeleton_tensorObj U V

theorem gammaIsoClassAt_surjective : Function.Surjective (gammaIsoClassAt (B := B) (S := S) (n := n)) := by
  intro a
  exact ⟨(fromSkeleton (GammaObjectAt B S n)).obj a.toMul,toSkeleton_fromSkeleton_obj a.toMul⟩

end IntegrationInACVF.Section6.FiniteRV
