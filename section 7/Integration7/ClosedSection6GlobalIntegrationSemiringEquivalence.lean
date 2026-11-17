module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalIntegrationUnit
public import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
public import Integration7.ClosedSection6GlobalQuotientAdditiveLift
public import Integration7.ClosedSection6FiniteVFIntegralScissors
public import Integration7.ClosedSection6GammaVFAllAdditivePresentation
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalIntegrationSemiringEquivalence
public import IntegrationSection6.GlobalIntegrationUnit
public import IntegrationSection6.GammaGlobalAdditiveLiftProducts
public import IntegrationSection6.GlobalQuotientAdditiveLift
public import IntegrationSection6.FiniteVFIntegralScissors
public import IntegrationSection6.GammaVFAllAdditivePresentation
public import IntegrationSection6.GammaVFAllFinitePresentation
public import IntegrationSection6.FiniteIntegrationPadding
public import IntegrationSection6.GammaNonzeroResolutions
public import IntegrationSection6.GammaNonzeroQuotientLift
public import IntegrationSection6.GammaNonzeroThroughTransitions
public import IntegrationSection6.GammaIspPadding

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

variable (hB : VFGammaGeneratedBase B)

variable {S : Set M}


@[instance_reducible] def gammaVFAllCommMonoid : CommMonoid (GammaVFAllAdditiveKPlus B) where
  mul a b := gammaVFProductBilinear a b
  one := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)
  mul_assoc a b c := by
    change gammaVFProductBilinear (gammaVFProductBilinear a b) c = gammaVFProductBilinear a (gammaVFProductBilinear b c)
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective
    rw [globalIntegration_product,globalIntegration_product,globalIntegration_product,globalIntegration_product,mul_assoc]
  one_mul a := by
    change gammaVFProductBilinear (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) a = a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective
    rw [globalIntegration_product,globalIntegration_one,one_mul]
  mul_one a := by
    change gammaVFProductBilinear a (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) = a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective
    rw [globalIntegration_product,globalIntegration_one,mul_one]
  mul_comm a b := by
    change gammaVFProductBilinear a b = gammaVFProductBilinear b a
    apply (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective
    rw [globalIntegration_product,globalIntegration_product,mul_comm]

@[instance_reducible] def gammaVFAllCommSemiring : CommSemiring (GammaVFAllAdditiveKPlus B) where
  toAddCommMonoid := inferInstance
  toCommMonoid := gammaVFAllCommMonoid hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
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
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    GammaVFAllAdditiveKPlus B ≃+* GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  exact {
    toEquiv := (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).toEquiv
    map_add' := map_add (globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)
    map_mul' := globalIntegration_product hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB }

theorem theorem_6_19_lift (U : GammaObjectAt B Set.univ k) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaAllAdditiveLiftClass U.toGamma) =
      (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) :=
  globalVFIntegration_lift_class hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U

end IntegrationInACVF.Section7.CompletedSection6
