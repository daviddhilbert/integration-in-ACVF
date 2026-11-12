import IntegrationSection6.GlobalIntegrationUnit
import IntegrationSection6.GammaGlobalAdditiveLiftProducts
import IntegrationSection6.GlobalQuotientAdditiveLift
import IntegrationSection6.FiniteVFIntegralScissors
import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.GammaVFAllFinitePresentation
import IntegrationSection6.FiniteIntegrationPadding
import IntegrationSection6.GammaNonzeroResolutions
import IntegrationSection6.GammaNonzeroQuotientLift
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

variable {S : Set M}

@[instance_reducible] def gammaVFAllCommMonoid : CommMonoid (GammaVFAllAdditiveKPlus B) where
  mul a b := gammaVFProductBilinear a b
  one := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)
  mul_assoc a b c := by
    change gammaVFProductBilinear (gammaVFProductBilinear a b) c = gammaVFProductBilinear a (gammaVFProductBilinear b c)
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective
    rw [globalIntegration_product,globalIntegration_product,globalIntegration_product,globalIntegration_product,mul_assoc]
  one_mul a := by
    change gammaVFProductBilinear (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) a = a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective
    rw [globalIntegration_product,globalIntegration_one,one_mul]
  mul_one a := by
    change gammaVFProductBilinear a (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) = a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective
    rw [globalIntegration_product,globalIntegration_one,mul_one]
  mul_comm a b := by
    change gammaVFProductBilinear a b = gammaVFProductBilinear b a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective
    rw [globalIntegration_product,globalIntegration_product,mul_comm]

@[instance_reducible] def gammaVFAllCommSemiring : CommSemiring (GammaVFAllAdditiveKPlus B) where
  toAddCommMonoid := inferInstance
  toCommMonoid := gammaVFAllCommMonoid hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  zero_mul a := congrArg (fun f : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B => f a) (map_zero gammaVFProductBilinear)
  mul_zero a := map_zero (gammaVFProductBilinear a)
  left_distrib a b c := map_add (gammaVFProductBilinear a) b c
  right_distrib a b c := congrArg (fun f : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B => f c) (map_add gammaVFProductBilinear a b)
  natCast n := n • PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul,one_nsmul]
    rfl

/-- Theorem6.19 for the requested RV[k] and RV[*] categories. The source
has its original scissor addition and actual Cartesian product. -/
def theorem_6_19 :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    GammaVFAllAdditiveKPlus B ≃+* GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  exact {
    toEquiv := (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).toEquiv
    map_add' := map_add (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)
    map_mul' := globalIntegration_product hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB }

theorem theorem_6_19_lift (U : GammaObjectAt B Set.univ k) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaAllAdditiveLiftClass U.toGamma) =
      (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) :=
  globalVFIntegration_lift_class hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U

end IntegrationInACVF.Section6.FiniteRV
