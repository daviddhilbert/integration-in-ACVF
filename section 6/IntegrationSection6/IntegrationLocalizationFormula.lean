import IntegrationSection6.IntegrationLocalizationEmbedding

/-! The normalization formula for the integration embedding. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Algebra Classical FirstOrder FirstOrder.Language
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

theorem integrationRingQuotientEquiv_lift (U : GammaObjectAt B Set.univ k) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)) =
        Ideal.Quotient.mk _ (GrothendieckAddGroup.ofRingHom
          (gammaNonzeroResolutionAt k (gammaIsoClassAt U))) := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  apply (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).injective
  change (gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)
      ((gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).symm
        (completionRingEquiv (theorem_6_19 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB)
          (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)))) = _
  rw [RingEquiv.apply_symm_apply,completionRingEquiv_of,theorem_6_19_lift,
    gammaNonzeroCompletionQuotientEquiv_of]

instance gammaJ_isLocalization : IsLocalization.Away (gammaJ (B := B)) (GammaNonzeroLocalization (B := B)) := by
  unfold gammaJ
  infer_instance

theorem theorem_6_22_lift (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U) :
    letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    theorem_6_22 hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma)) =
      algebraMap (GammaNonzeroCompletion (B := B)) (GammaNonzeroLocalization (B := B))
        (CompletionLocalization.homogeneous k (gammaNonzeroClassAt U hU)) *
          IsLocalization.Away.invSelf (gammaJ (B := B)) ^ k := by
  letI := gammaVFAllCommSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  change CompletionLocalization.quotientEmbedding gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt
    (integrationRingQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (GrothendieckAddGroup.ofRingHom (gammaAllAdditiveLiftClass U.toGamma))) = _
  rw [integrationRingQuotientEquiv_lift]
  have he := gammaNonzeroResolutionAt_pure k (gammaNonzeroClassAt U hU)
  change gammaNonzeroResolutionAt k (gammaIsoClassAt U) = _ at he
  rw [he]
  exact CompletionLocalization.quotientEmbedding_mk_homogeneous _ _ k _

end IntegrationInACVF.Section6.FiniteRV
