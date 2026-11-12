import IntegrationSection6.GlobalVFIntegrationMap
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

theorem globalVFIntegration_lift_class (U : GammaObjectAt B Set.univ k) :
    globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaAllAdditiveLiftClass U.toGamma) =
      (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) := by
  rw [gammaAllAdditiveLiftClass,globalVFIntegration_class,globalVFAllIntegralValue_from_bounded]
  unfold globalVFIntegralAt
  rw [vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 _ U.toGamma
    (gammaIso_reflexive U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable)]
  exact integrationTargetToGlobal_class hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U

theorem globalVFIntegration_after_lifting :
    (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).comp
      (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨a,rfl⟩ := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk'_surjective a
  obtain ⟨k,x,rfl⟩ := gammaThroughToGradedAt_exhaustive a
  obtain ⟨U,hU⟩ := gammaIsoClassAt_surjective (gammaFiniteWeightAssemblyAt k x)
  have hr : gammaNonzeroResolutionAt k (gammaIsoClassAt U) = gammaThroughToGradedAt k x := by
    rw [hU,gammaNonzeroResolutionAt_assembly]
  change globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).mk' (gammaThroughToGradedAt k x))) = _
  rw [← hr,globalQuotientAdditiveLift_class,globalVFIntegration_lift_class]
  rfl

theorem globalLifting_after_integration :
    (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).comp
      (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) = AddMonoidHom.id _ := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaVFAllAdditivePresentation B)
  intro A
  let R := finiteVFLiftRepresentative hκ hs h00 hreal FBase (gammaVFAllBounded A)
  let U := gammaUniversalObject R.1
  let e : GammaIso B A.domain U.toGamma.lift := R.2
  have hV := vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 (gammaVFAllBounded A) U.toGamma e
  change globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (PositiveAdditiveGrothendieck.of _ A)) = _
  rw [globalVFIntegration_class]
  change globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A.arity.1
      (vfIntegralValue hκ hs h00 hreal FBase (gammaVFAllBounded A))) = _
  rw [hV,integrationTargetToGlobal_class,globalQuotientAdditiveLift_class]
  exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e⟩).symm

def globalAdditiveIntegrationEquiv : GammaVFAllAdditiveKPlus B ≃+
    GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB where
  toFun := globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  invFun := globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  left_inv x := DFunLike.congr_fun (globalLifting_after_integration hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) x
  right_inv x := DFunLike.congr_fun (globalVFIntegration_after_lifting hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB) x
  map_add' := map_add _

end IntegrationInACVF.Section6.FiniteRV
