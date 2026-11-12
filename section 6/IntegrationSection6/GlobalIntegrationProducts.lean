import IntegrationSection6.GammaNonzeroIspSemiring
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

abbrev GlobalIntegrationSemiringTarget :=
  (gammaNonzeroIspUnionRingCon (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).Quotient

def globalAdditiveIntegrationToSemiring : GammaVFAllAdditiveKPlus B ≃+
    GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB :=
  globalAdditiveIntegrationEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB

theorem globalIntegration_lift_value (a : GammaNonzeroGradedAt (B := B) (S := Set.univ)) :
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB a) =
        (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk' a :=
  DFunLike.congr_fun (globalVFIntegration_after_lifting hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)
    ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk' a)

theorem globalIntegration_product (a b : GammaVFAllAdditiveKPlus B) :
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaVFProductBilinear a b) =
      globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB a *
        globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB b := by
  let E := globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  obtain ⟨x,hx⟩ := (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'_surjective (E a)
  obtain ⟨y,hy⟩ := (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'_surjective (E b)
  have hxa : gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB x = a :=
    (congrArg E.symm hx).trans (E.symm_apply_apply a)
  have hyb : gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB y = b :=
    (congrArg E.symm hy).trans (E.symm_apply_apply b)
  rw [← hxa,← hyb,← gammaNonzeroGlobalAdditiveLiftAt_product,
    globalIntegration_lift_value,globalIntegration_lift_value,globalIntegration_lift_value,map_mul]

end IntegrationInACVF.Section6.FiniteRV
