module

public import IntegrationSection6.GammaNonzeroPrincipalIdeal
public import IntegrationSection6.CompletionRingEquivalences
public import IntegrationSection6.GammaNonzeroBasicRelation
public import IntegrationSection6.GroupifiedCongruence
public import IntegrationSection6.CompletionLocalization
public import IntegrationSection6.GammaNonzeroBasicClasses
public import IntegrationSection6.GammaGradedResolution
public import IntegrationSection6.FiniteGammaBasicGenerators
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

/-! The nonzero-coordinate filtered form of fixed-degree integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Algebra Classical FirstOrder FirstOrder.Language
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

def integrationRingQuotientEquiv :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) ≃+*
      (GammaNonzeroCompletion (B := B) ⧸ CompletionLocalization.relationIdeal
        (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  exact (completionRingEquiv (theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)).trans
    (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).symm

/-- Theorem6.22: the actual finite VF Grothendieck ring embeds into the
localization of the nonzero graded RV ring at j. -/
def theorem_6_22 :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) →+* GammaNonzeroLocalization (B := B) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  exact (CompletionLocalization.quotientEmbedding gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt).comp
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).toRingHom

theorem theorem_6_22_injective :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    Function.Injective (theorem_6_22 (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  exact (CompletionLocalization.quotientEmbedding_injective gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt).comp
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective

end IntegrationInACVF.Section6.FiniteRV
