module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6IntegrationLocalizationEmbedding
public import IntegrationSection6.IntegrationLocalizationFormula
public import IntegrationSection6.IntegrationLocalizationEmbedding

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Algebra Classical FirstOrder FirstOrder.Language
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


theorem integrationRingQuotientEquiv_lift (U : GammaObjectAt B Set.univ k) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)) =
        Ideal.Quotient.mk _ (GrothendieckAddGroup.ofRingHom
          (gammaNonzeroResolutionAt k (gammaIsoClassAt U))) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  apply (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).injective
  change (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)
      ((gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).symm
        (completionRingEquiv (theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)
          (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)))) = _
  rw [RingEquiv.apply_symm_apply,completionRingEquiv_of,theorem_6_19_lift,
    gammaNonzeroCompletionQuotientEquiv_of]

instance gammaJ_isLocalization : IsLocalization.Away (gammaJ (B := B)) (GammaNonzeroLocalization (B := B)) := by
  unfold gammaJ
  infer_instance

theorem theorem_6_22_lift (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    theorem_6_22 hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)) =
      algebraMap (GammaNonzeroCompletion (B := B)) (GammaNonzeroLocalization (B := B))
        (CompletionLocalization.homogeneous k (gammaNonzeroClassAt U hU)) *
          IsLocalization.Away.invSelf (gammaJ (B := B)) ^ k := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  change CompletionLocalization.quotientEmbedding gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma))) = _
  rw [integrationRingQuotientEquiv_lift]
  have he := gammaNonzeroResolutionAt_pure k (gammaNonzeroClassAt U hU)
  change gammaNonzeroResolutionAt k (gammaIsoClassAt U) = _ at he
  rw [he]
  exact CompletionLocalization.quotientEmbedding_mk_homogeneous _ _ k _

end IntegrationInACVF.Section7.CompletedSection6
