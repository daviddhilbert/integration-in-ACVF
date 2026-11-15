import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GammaNonzeroBasicGeneration
import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
import Integration7.ClosedSection6GlobalQuotientAdditiveLift
import Integration7.ClosedSection6FiniteVFIntegralScissors
import Integration7.ClosedSection6GammaVFAllAdditivePresentation
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import Integration7.ClosedSection6FiniteIntegrationPadding
import Integration7.ClosedSection6GammaNonzeroQuotientLift
import Integration7.ClosedSection6GammaIspPadding
import IntegrationSection6.GammaNonzeroBasicRelation
import IntegrationSection6.GammaNonzeroBasicGeneration
import IntegrationSection6.GammaNonzeroBasicClasses
import IntegrationSection6.GammaGradedResolution
import IntegrationSection6.FiniteGammaBasicGenerators
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


def gammaNonzeroBasicRelation (a b : GammaNonzeroGradedAt (B := B) (S := Set.univ)) : Prop :=
  a = DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt ∧
  b = 1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt

theorem gammaNonzeroIsp_eq_basic :
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB =
      ringConGen (gammaNonzeroBasicRelation (B := B)) := by
  rw [gammaNonzeroIsp_eq_resolved_basic]
  congr 1
  funext a b
  unfold gammaResolvedBasicRelation gammaNonzeroBasicRelation
  rw [gammaGradedResolutionAt_one_factor,gammaGradedResolutionAt_positive_factor]

end IntegrationInACVF.Section7.CompletedSection6
