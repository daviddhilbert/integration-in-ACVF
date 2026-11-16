module

public import IntegrationSection6.GammaNonzeroBasicGeneration
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

@[expose] public section

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

def gammaNonzeroBasicRelation (a b : GammaNonzeroGradedAt (B := B) (S := Set.univ)) : Prop :=
  a = DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt ∧
  b = 1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt

theorem gammaNonzeroIsp_eq_basic :
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB =
      ringConGen (gammaNonzeroBasicRelation (B := B)) := by
  rw [gammaNonzeroIsp_eq_resolved_basic]
  congr 1
  funext a b
  unfold gammaResolvedBasicRelation gammaNonzeroBasicRelation
  rw [gammaGradedResolutionAt_one_factor,gammaGradedResolutionAt_positive_factor]

end IntegrationInACVF.Section6.FiniteRV
