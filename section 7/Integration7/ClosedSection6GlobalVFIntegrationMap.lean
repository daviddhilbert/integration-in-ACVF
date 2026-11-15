import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GlobalVFIntegralValues
import Integration7.ClosedSection6FiniteVFIntegralScissors
import Integration7.ClosedSection6GammaVFAllAdditivePresentation
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import Integration7.ClosedSection6FiniteIntegrationPadding
import Integration7.ClosedSection6GammaNonzeroQuotientLift
import Integration7.ClosedSection6GammaIspPadding
import IntegrationSection6.GlobalVFIntegrationMap
import IntegrationSection6.GlobalVFIntegralValues
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


theorem globalVFAllIntegralValue_scissor {A C D E : GammaVFAllFiniteObject B}
    (h : GammaVFAllScissor A C D E) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A +
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB C =
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB D +
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB E := by
  rcases A with ⟨⟨n,a⟩,A,hA,fA⟩
  rcases C with ⟨c,C,hC,fC⟩
  rcases D with ⟨d,D,hD,fD⟩
  rcases E with ⟨e,E,hE,fE⟩
  rcases h with ⟨hc,hd,he,hu,hi⟩
  change (n,a) = c at hc
  change (n,a) = d at hd
  change (n,a) = e at he
  subst c; subst d; subst e
  let AA : GammaVFAllFiniteObject B := ⟨(n,a),A,hA,fA⟩
  let CC : GammaVFAllFiniteObject B := ⟨(n,a),C,hC,fC⟩
  let DD : GammaVFAllFiniteObject B := ⟨(n,a),D,hD,fD⟩
  let EE : GammaVFAllFiniteObject B := ⟨(n,a),E,hE,fE⟩
  have hsc : GammaVFScissor (gammaVFAllBounded AA).val (gammaVFAllBounded CC).val
      (gammaVFAllBounded DD).val (gammaVFAllBounded EE).val := ⟨rfl,rfl,rfl,hu,hi⟩
  have H := congrArg (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB n)
    ((vfIntegralValue_scissor (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hsc)
  simpa only [map_add,globalVFAllIntegralValue,globalVFIntegralAt,AA,CC,DD,EE] using H

def globalVFIntegralInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B)
    (A := GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) where
  toFun := globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  iso := fun ⟨e⟩ => globalVFAllIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB e
  empty := globalVFAllIntegralValue_empty hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  scissor := fun h => globalVFAllIntegralValue_scissor hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB h

def globalVFIntegration : GammaVFAllAdditiveKPlus B →+
    GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB :=
  PositiveAdditiveGrothendieck.lift _ (globalVFIntegralInvariant hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)

theorem globalVFIntegration_class (A : GammaVFAllFiniteObject B) :
    globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A) =
        globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

end IntegrationInACVF.Section7.CompletedSection6
