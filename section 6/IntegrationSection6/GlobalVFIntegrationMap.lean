import IntegrationSection6.GlobalVFIntegralValues
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

theorem globalVFAllIntegralValue_scissor {A C D E : GammaVFAllFiniteObject B}
    (h : GammaVFAllScissor A C D E) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A +
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB C =
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB D +
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB E := by
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
  have H := congrArg (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB n)
    (vfIntegralValue_scissor hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hsc)
  simpa only [map_add,globalVFAllIntegralValue,globalVFIntegralAt,AA,CC,DD,EE] using H

def globalVFIntegralInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B)
    (A := GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) where
  toFun := globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  iso := fun ⟨e⟩ => globalVFAllIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB e
  empty := globalVFAllIntegralValue_empty hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  scissor := fun h => globalVFAllIntegralValue_scissor hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB h

def globalVFIntegration : GammaVFAllAdditiveKPlus B →+
    GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB :=
  PositiveAdditiveGrothendieck.lift _ (globalVFIntegralInvariant hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)

theorem globalVFIntegration_class (A : GammaVFAllFiniteObject B) :
    globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A) =
        globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

end IntegrationInACVF.Section6.FiniteRV
