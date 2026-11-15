import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GlobalIntegrationCharacterization
import Integration7.ClosedSection6GammaNonzeroBasicRelation
import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
import Integration7.ClosedSection6GlobalQuotientAdditiveLift
import Integration7.ClosedSection6FiniteVFIntegralScissors
import Integration7.ClosedSection6GammaVFAllAdditivePresentation
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import Integration7.ClosedSection6FiniteIntegrationPadding
import Integration7.ClosedSection6GammaNonzeroQuotientLift
import Integration7.ClosedSection6GammaIspPadding
import IntegrationSection6.GammaNonzeroPrincipalIdeal
import IntegrationSection6.GlobalIntegrationCharacterization
import IntegrationSection6.GammaNonzeroBasicRelation
import IntegrationSection6.GroupifiedCongruence
import IntegrationSection6.CompletionLocalization
import IntegrationSection6.GammaNonzeroBasicClasses
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


abbrev GammaNonzeroCompletion := CompletionLocalization.Ring (GammaNonzeroClassesAt (B := B) (S := Set.univ))

def gammaJ : GammaNonzeroCompletion (B := B) := CompletionLocalization.pivot
  (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))

abbrev GammaNonzeroLocalization := CompletionLocalization.Target
  (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))

def gammaJRelationIdeal : Ideal (GammaNonzeroCompletion (B := B)) := Ideal.span {gammaJ (B := B) - 1}

theorem gammaNonzeroIsp_relationIdeal :
    GroupifiedCongruence.relationIdeal (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) =
      CompletionLocalization.relationIdeal (gammaNonzeroOneClassAt (B := B) (S := Set.univ))
        (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ)) := by
  rw [gammaNonzeroIsp_eq_basic]
  change GroupifiedCongruence.relationIdeal (ringConGen (fun a b =>
    a = DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt ∧
    b = 1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt)) = _
  rw [GroupifiedCongruence.relationIdeal_singleton]
  have he : GrothendieckAddGroup.ofRingHom (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt) -
      GrothendieckAddGroup.ofRingHom (1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt) =
      CompletionLocalization.pivot (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ)) - 1 := by
    simp only [map_add,map_one,CompletionLocalization.pivot,CompletionLocalization.homogeneous]
    abel
  unfold CompletionLocalization.relationIdeal
  rw [he]

theorem gammaNonzeroIsp_relationIdeal_j :
    GroupifiedCongruence.relationIdeal (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) =
      gammaJRelationIdeal (B := B) := gammaNonzeroIsp_relationIdeal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB

def gammaNonzeroCompletionQuotientMap :
    (GammaNonzeroCompletion (B := B) ⧸ CompletionLocalization.relationIdeal
      (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))) →+*
      GrothendieckAddGroup (GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) :=
  Ideal.Quotient.lift _ (GroupifiedCongruence.completionMap
    (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB)) (by
      intro x hx
      rw [← gammaNonzeroIsp_relationIdeal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB] at hx
      exact RingHom.mem_ker.mp (GroupifiedCongruence.relationIdeal_le_ker _ hx))

def gammaNonzeroCompletionQuotientEquiv :
    (GammaNonzeroCompletion (B := B) ⧸ CompletionLocalization.relationIdeal
      (gammaNonzeroOneClassAt (B := B) (S := Set.univ)) (gammaNonzeroPositiveClassAt (B := B) (S := Set.univ))) ≃+*
      GrothendieckAddGroup (GlobalIntegrationSemiringTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) :=
  RingEquiv.ofBijective (gammaNonzeroCompletionQuotientMap hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) ⟨by
    apply RingHom.lift_injective_of_ker_le_ideal
    rw [GroupifiedCongruence.completionMap_kernel,gammaNonzeroIsp_relationIdeal],by
    intro x
    obtain ⟨a,ha⟩ := GroupifiedCongruence.completionMap_surjective
      (gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB) x
    exact ⟨Ideal.Quotient.mk _ a,ha⟩⟩

theorem gammaNonzeroCompletionQuotientEquiv_of (a : GammaNonzeroGradedAt (B := B) (S := Set.univ)) :
    gammaNonzeroCompletionQuotientEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (Ideal.Quotient.mk _ (GrothendieckAddGroup.ofRingHom a)) =
        GrothendieckAddGroup.ofRingHom ((gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk' a) :=
  GroupifiedCongruence.completionMap_of _ a

end IntegrationInACVF.Section7.CompletedSection6
