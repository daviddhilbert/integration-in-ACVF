import IntegrationSection6.GlobalIntegrationTarget
import IntegrationSection6.GammaGlobalAdditiveLift
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

theorem gammaGlobalAdditiveLift_respects_union :
    gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB ≤
      AddCon.ker (gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ hs h00 hreal hB) := by
  rintro a b ⟨n,x,y,rfl,rfl,H⟩
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaThroughToGradedAt n x) =
    gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaThroughToGradedAt n y)
  rw [gammaNonzeroGlobalAdditiveLiftAt_through,gammaNonzeroGlobalAdditiveLiftAt_through]
  change gammaClassIspAt hκ hs h00 hreal (gammaFiniteWeightAssemblyAt n x) (gammaFiniteWeightAssemblyAt n y) at H
  obtain ⟨U,V,hU,hV,G⟩ := H
  rw [← hU,← hV,gammaAllAdditiveLiftClassesAt_class,gammaAllAdditiveLiftClassesAt_class]
  exact PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) (G.liftIsoNative hB)

def globalQuotientAdditiveLift : GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB →+
    GammaVFAllAdditiveKPlus B :=
  (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).lift
    (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB)
    (gammaGlobalAdditiveLift_respects_union hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)

theorem globalQuotientAdditiveLift_class (U : GammaObjectAt B Set.univ k) :
    globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U))) = gammaAllAdditiveLiftClass U.toGamma := by
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) = _
  rw [gammaNonzeroGlobalAdditiveLiftAt_resolution,gammaAllAdditiveLiftClassesAt_class]

end IntegrationInACVF.Section6.FiniteRV
