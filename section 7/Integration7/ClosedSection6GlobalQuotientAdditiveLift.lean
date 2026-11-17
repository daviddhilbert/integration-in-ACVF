module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalIntegrationTarget
public import Integration7.ClosedSection6GammaGlobalAdditiveLift
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalQuotientAdditiveLift
public import IntegrationSection6.GlobalIntegrationTarget
public import IntegrationSection6.GammaGlobalAdditiveLift
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


theorem gammaGlobalAdditiveLift_respects_union :
    gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB ≤
      AddCon.ker (gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ hs h00 hreal hB) := by
  rintro a b ⟨n,x,y,rfl,rfl,H⟩
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaThroughToGradedAt n x) =
    gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaThroughToGradedAt n y)
  rw [gammaNonzeroGlobalAdditiveLiftAt_through,gammaNonzeroGlobalAdditiveLiftAt_through]
  change gammaClassIspAt hκ hs h00 hreal (gammaFiniteWeightAssemblyAt n x) (gammaFiniteWeightAssemblyAt n y) at H
  obtain ⟨U,V,hU,hV,G⟩ := H
  rw [← hU,← hV,gammaAllAdditiveLiftClassesAt_class,gammaAllAdditiveLiftClassesAt_class]
  exact PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) (G.liftIsoNative hB)

def globalQuotientAdditiveLift : GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB →+
    GammaVFAllAdditiveKPlus B :=
  (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).lift
    (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB)
    (gammaGlobalAdditiveLift_respects_union hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)

theorem globalQuotientAdditiveLift_class (U : GammaObjectAt B Set.univ k) :
    globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U))) = gammaAllAdditiveLiftClass U.toGamma := by
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) = _
  rw [gammaNonzeroGlobalAdditiveLiftAt_resolution,gammaAllAdditiveLiftClassesAt_class]

end IntegrationInACVF.Section7.CompletedSection6
