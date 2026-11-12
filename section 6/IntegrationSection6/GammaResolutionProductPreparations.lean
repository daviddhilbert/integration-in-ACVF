import IntegrationSection6.GammaResolutionWeightedIsomorphisms
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

theorem gammaResolution_product_padding_left {k l : ℕ} (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaNonzeroResolutionAt ((k+1)+l) (gammaClassMulAt (gammaPaddingClassesAt a) b) =
      gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a b) := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaPaddingClassesAt_class,gammaClassMulAt_class,gammaClassMulAt_class]
  exact gammaNonzeroResolutionAt_weightedIso _ _ (gammaWeightedPadProductLeftAt U V)

theorem gammaResolution_product_padding_right {k l : ℕ} (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaNonzeroResolutionAt (k+(l+1)) (gammaClassMulAt a (gammaPaddingClassesAt b)) =
      gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a b) := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaPaddingClassesAt_class,gammaClassMulAt_class,gammaClassMulAt_class]
  exact gammaNonzeroResolutionAt_weightedIso _ _ (gammaWeightedPadProductRightAt U V)

theorem gammaResolution_product_pure_pure {k l : ℕ}
    (a : GammaNonzeroClassesAt (B := B) (S := S) k) (b : GammaNonzeroClassesAt (B := B) (S := S) l) :
    gammaNonzeroResolutionAt (k+l) (gammaClassMulAt a.val b.val) =
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) k a *
        DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) l b := by
  rw [DirectSum.of_mul_of]
  exact gammaNonzeroResolutionAt_pure (k+l) (gammaNonzeroMulAt a b)

end IntegrationInACVF.Section6.FiniteRV
