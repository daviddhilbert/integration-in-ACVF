import IntegrationSection6.GammaNonzeroIspSemiring
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

theorem gammaNonzeroIsp_least_resolved_basic (q : RingCon (GammaNonzeroGradedAt (B := B) (S := Set.univ)))
    (hbasic : q (gammaGradedResolutionAt (gammaGradedClassAt (gammaOneAt (Set.subset_univ _))))
      (gammaGradedResolutionAt (gammaGradedClassAt (gammaPositiveAt (Set.subset_univ _))))) :
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB ≤ q := by
  have hq := gammaIspRingConAt_least_basic hκ hs h00 hreal (q.comap gammaGradedResolutionAt) hbasic
  rintro a b ⟨n,x,y,rfl,rfl,H⟩
  change gammaClassIspAt hκ hs h00 hreal (gammaFiniteWeightAssemblyAt n x) (gammaFiniteWeightAssemblyAt n y) at H
  obtain ⟨U,V,hU,hV,G⟩ := H
  have hg := hq ((gammaIspRingConAt_class_iff hκ hs h00 hreal U V).mpr G)
  change q (gammaGradedResolutionAt (gammaGradedClassAt U)) (gammaGradedResolutionAt (gammaGradedClassAt V)) at hg
  simp only [gammaGradedClassAt,gammaGradedResolutionAt_of] at hg
  rw [hU,hV,gammaNonzeroResolutionAt_assembly,gammaNonzeroResolutionAt_assembly] at hg
  exact hg

def gammaResolvedBasicRelation (a b : GammaNonzeroGradedAt (B := B) (S := Set.univ)) : Prop :=
  a = gammaGradedResolutionAt (gammaGradedClassAt (gammaOneAt (B := B) (Set.subset_univ _))) ∧
  b = gammaGradedResolutionAt (gammaGradedClassAt (gammaPositiveAt (B := B) (Set.subset_univ _)))

theorem gammaNonzeroIsp_eq_resolved_basic :
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB =
      ringConGen (gammaResolvedBasicRelation (B := B)) := by
  apply le_antisymm
  · apply gammaNonzeroIsp_least_resolved_basic hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    exact RingConGen.Rel.of _ _ ⟨rfl,rfl⟩
  · apply RingCon.ringConGen_le.mpr
    rintro a b ⟨rfl,rfl⟩
    change gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB _ _
    simp only [gammaGradedClassAt,gammaGradedResolutionAt_of]
    refine ⟨1,(gammaFiniteWeightAssemblyAt 1).symm (gammaIsoClassAt (gammaOneAt (Set.subset_univ _))),
      (gammaFiniteWeightAssemblyAt 1).symm (gammaIsoClassAt (gammaPositiveAt (Set.subset_univ _))),rfl,rfl,?_⟩
    change gammaClassIspAt hκ hs h00 hreal
      (gammaFiniteWeightAssemblyAt 1 ((gammaFiniteWeightAssemblyAt 1).symm _))
      (gammaFiniteWeightAssemblyAt 1 ((gammaFiniteWeightAssemblyAt 1).symm _))
    rw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
    exact (gammaClassIspAt_class_iff _ _).mpr (gammaBasic_ispAt hκ hs h00 hreal (Set.subset_univ _))

end IntegrationInACVF.Section6.FiniteRV
