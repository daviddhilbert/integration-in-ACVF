module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaNonzeroIspSemiring
public import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
public import Integration7.ClosedSection6GlobalQuotientAdditiveLift
public import Integration7.ClosedSection6FiniteVFIntegralScissors
public import Integration7.ClosedSection6GammaVFAllAdditivePresentation
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalIntegrationProducts
public import IntegrationSection6.GammaNonzeroIspSemiring
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


abbrev GlobalIntegrationSemiringTarget :=
  (gammaNonzeroIspUnionRingCon (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).Quotient

def globalAdditiveIntegrationToSemiring : GammaVFAllAdditiveKPlus B ≃+
    GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB :=
  globalAdditiveIntegrationEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB

theorem globalIntegration_lift_value (a : GammaNonzeroGradedAt (B := B) (S := Set.univ)) :
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB a) =
        (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk' a :=
  DFunLike.congr_fun (globalVFIntegration_after_lifting hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)
    ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk' a)

theorem globalIntegration_product (a b : GammaVFAllAdditiveKPlus B) :
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFProductBilinear a b) =
      globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB a *
        globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB b := by
  let E := globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  obtain ⟨x,hx⟩ := (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'_surjective (E a)
  obtain ⟨y,hy⟩ := (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'_surjective (E b)
  have hxa : gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB x = a :=
    (congrArg E.symm hx).trans (E.symm_apply_apply a)
  have hyb : gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB y = b :=
    (congrArg E.symm hy).trans (E.symm_apply_apply b)
  rw [← hxa,← hyb,← gammaNonzeroGlobalAdditiveLiftAt_product,
    globalIntegration_lift_value,globalIntegration_lift_value,globalIntegration_lift_value,map_mul]

end IntegrationInACVF.Section7.CompletedSection6
