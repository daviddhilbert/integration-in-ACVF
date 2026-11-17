module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalVFIntegrationMap
public import Integration7.ClosedSection6GlobalQuotientAdditiveLift
public import Integration7.ClosedSection6FiniteVFIntegralScissors
public import Integration7.ClosedSection6GammaVFAllAdditivePresentation
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalAdditiveIntegrationEquivalence
public import IntegrationSection6.GlobalVFIntegrationMap
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


theorem globalVFIntegration_lift_class (U : GammaObjectAt B Set.univ k) :
    globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaAllAdditiveLiftClass U.toGamma) =
      (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) := by
  rw [gammaAllAdditiveLiftClass,globalVFIntegration_class,globalVFAllIntegralValue_from_bounded]
  unfold globalVFIntegralAt
  rw [(vfIntegralValue_of_lift_representation (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc _ U.toGamma
    (gammaIso_reflexive U.toGamma.lift U.toGamma.toGammaRVObject.lift_definable)]
  exact integrationTargetToGlobal_class hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB U

theorem globalVFIntegration_after_lifting :
    (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).comp
      (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨a,rfl⟩ := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'_surjective a
  obtain ⟨k,x,rfl⟩ := gammaThroughToGradedAt_exhaustive a
  obtain ⟨U,hU⟩ := gammaIsoClassAt_surjective (gammaFiniteWeightAssemblyAt k x)
  have hr : gammaNonzeroResolutionAt k (gammaIsoClassAt U) = gammaThroughToGradedAt k x := by
    rw [hU,gammaNonzeroResolutionAt_assembly]
  change globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk' (gammaThroughToGradedAt k x))) = _
  rw [← hr,globalQuotientAdditiveLift_class,globalVFIntegration_lift_class]
  rfl

theorem globalLifting_after_integration :
    (globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).comp
      (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) = AddMonoidHom.id _ := by
  apply PositiveAdditiveGrothendieck.hom_ext (gammaVFAllAdditivePresentation B)
  intro A
  let R := (finiteVFLiftRepresentative (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase (gammaVFAllBounded A)
  let U := gammaUniversalObject R.1
  let e : GammaIso B A.domain U.toGamma.lift := R.2
  have hV := (vfIntegralValue_of_lift_representation (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc (gammaVFAllBounded A) U.toGamma e
  change globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (PositiveAdditiveGrothendieck.of _ A)) = _
  rw [globalVFIntegration_class]
  change globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A.arity.1
      ((vfIntegralValue (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase (gammaVFAllBounded A))) = _
  rw [hV,integrationTargetToGlobal_class,globalQuotientAdditiveLift_class]
  exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e⟩).symm

def globalAdditiveIntegrationEquiv : GammaVFAllAdditiveKPlus B ≃+
    GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB where
  toFun := globalVFIntegration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  invFun := globalQuotientAdditiveLift hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  left_inv x := DFunLike.congr_fun (globalLifting_after_integration hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) x
  right_inv x := DFunLike.congr_fun (globalVFIntegration_after_lifting hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) x
  map_add' := map_add _

end IntegrationInACVF.Section7.CompletedSection6
