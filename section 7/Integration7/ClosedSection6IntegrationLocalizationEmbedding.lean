import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GammaNonzeroPrincipalIdeal
import Integration7.ClosedSection6GammaNonzeroBasicRelation
import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
import Integration7.ClosedSection6GlobalQuotientAdditiveLift
import Integration7.ClosedSection6FiniteVFIntegralScissors
import Integration7.ClosedSection6GammaVFAllAdditivePresentation
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import Integration7.ClosedSection6FiniteIntegrationPadding
import Integration7.ClosedSection6GammaNonzeroQuotientLift
import Integration7.ClosedSection6GammaIspPadding
import IntegrationSection6.IntegrationLocalizationEmbedding
import IntegrationSection6.GammaNonzeroPrincipalIdeal
import IntegrationSection6.CompletionRingEquivalences
import IntegrationSection6.GammaNonzeroBasicRelation
import IntegrationSection6.GroupifiedCongruence
import IntegrationSection6.CompletionLocalization
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
open Algebra Classical FirstOrder FirstOrder.Language
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


def integrationRingQuotientEquiv :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) ≃+*
      (GammaNonzeroCompletion (B := B) ⧸ CompletionLocalization.relationIdeal
        (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  exact (completionRingEquiv (theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)).trans
    (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).symm

/-- Theorem6.22: the actual finite VF Grothendieck ring embeds into the
localization of the nonzero graded RV ring at j. -/
def theorem_6_22 :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) →+* GammaNonzeroLocalization (B := B) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  exact (CompletionLocalization.quotientEmbedding gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt).comp
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).toRingHom

theorem theorem_6_22_injective :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    Function.Injective (theorem_6_22 (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  exact (CompletionLocalization.quotientEmbedding_injective gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt).comp
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective

end IntegrationInACVF.Section7.CompletedSection6
