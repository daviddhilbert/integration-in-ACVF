import IntegrationSection6.GammaResolutionProductPreparations
import IntegrationSection6.GammaWeightedPaddingProducts
import IntegrationSection6.GammaWeightDecomposition
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

variable [Fact (B.real ⊆ S)]

theorem gammaResolution_through_product_pure (k l : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k)
    (b : GammaNonzeroClassesAt (B := B) (S := S) l) :
    gammaNonzeroResolutionAt (k+l) (gammaClassMulAt (gammaFiniteWeightAssemblyAt k a) b.val) =
      gammaThroughToGradedAt k a * DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) l b := by
  induction k with
  | zero => exact gammaResolution_product_pure_pure a b
  | succ n ih =>
    rw [gammaFiniteWeightAssemblyAt_succ,gammaClassMulAt_add_left,map_add,gammaResolution_product_padding_left,ih,
      gammaResolution_product_pure_pure]
    change gammaThroughToGradedAt n a.1 * DirectSum.of _ l b + DirectSum.of _ (n+1) a.2 * DirectSum.of _ l b =
      (gammaThroughToGradedAt n a.1 + DirectSum.of _ (n+1) a.2) * DirectSum.of _ l b
    exact (add_mul _ _ _).symm

theorem gammaResolution_product_pure {k l : ℕ} (a : GammaIsoClassesAt B S k)
    (b : GammaNonzeroClassesAt (B := B) (S := S) l) :
    gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a b.val) =
      gammaNonzeroResolutionAt k a * DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) l b := by
  have H := gammaResolution_through_product_pure k l ((gammaFiniteWeightAssemblyAt k).symm a) b
  rw [AddEquiv.apply_symm_apply] at H
  exact H

theorem gammaResolution_product_through {k : ℕ} (a : GammaIsoClassesAt B S k) (l : ℕ)
    (b : GammaNonzeroThroughAt (B := B) (S := S) l) :
    gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a (gammaFiniteWeightAssemblyAt l b)) =
      gammaNonzeroResolutionAt k a * gammaThroughToGradedAt l b := by
  induction l with
  | zero => exact gammaResolution_product_pure a b
  | succ n ih =>
    rw [gammaFiniteWeightAssemblyAt_succ,gammaClassMulAt_add,map_add,gammaResolution_product_padding_right,ih,
      gammaResolution_product_pure]
    change gammaNonzeroResolutionAt k a * gammaThroughToGradedAt n b.1 + gammaNonzeroResolutionAt k a * DirectSum.of _ (n+1) b.2 =
      gammaNonzeroResolutionAt k a * (gammaThroughToGradedAt n b.1 + DirectSum.of _ (n+1) b.2)
    exact (mul_add _ _ _).symm

theorem gammaNonzeroResolutionAt_product {k l : ℕ} (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a b) = gammaNonzeroResolutionAt k a * gammaNonzeroResolutionAt l b := by
  have H := gammaResolution_product_through a l ((gammaFiniteWeightAssemblyAt l).symm b)
  rw [AddEquiv.apply_symm_apply] at H
  exact H

end IntegrationInACVF.Section6.FiniteRV
