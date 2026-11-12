import IntegrationSection6.FiniteGammaBasicGenerators
import IntegrationSection6.GroupifiedCongruence

/-! Actual principal ideal in the group completion of the graded sum of
full finite RV[k] classes. The positive factor includes zero in degree one.
This is the homogeneous comparison, before the nonzero-label compression
and j-1 localization required by the complete theorem6.22. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language Algebra
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} [hBS : Fact (B.real ⊆ S)]

abbrev GammaGradedCompletionAt (B : Base (M := M)) (S : Set M) [Fact (B.real ⊆ S)] :=
  GrothendieckAddGroup (GammaGradedClassesAt B S)

def gammaHomogeneousGeneratorAt : GammaGradedCompletionAt B S :=
  GrothendieckAddGroup.ofRingHom (gammaGradedClassAt (gammaOneAt hBS.out)) -
    GrothendieckAddGroup.ofRingHom (gammaGradedClassAt (gammaPositiveAt hBS.out))

def gammaHomogeneousIdealAt : Ideal (GammaGradedCompletionAt B S) :=
  Ideal.span {gammaHomogeneousGeneratorAt (B := B) (S := S)}

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)

theorem gammaIsp_relationIdeal_principal :
    GroupifiedCongruence.relationIdeal (gammaIspRingConAt (S := S) hκ hs h00 hsmall) =
      gammaHomogeneousIdealAt (B := B) (S := S) := by
  rw [gammaIspRingConAt_eq_basic]
  exact GroupifiedCongruence.relationIdeal_singleton _ _

theorem gammaIsp_completionMap_kernel :
    RingHom.ker (GroupifiedCongruence.completionMap (gammaIspRingConAt (S := S) hκ hs h00 hsmall)) =
      gammaHomogeneousIdealAt (B := B) (S := S) :=
  (GroupifiedCongruence.completionMap_kernel _).trans (gammaIsp_relationIdeal_principal hκ hs h00 hsmall)

def gammaHomogeneousQuotientEquiv :
    (GammaGradedCompletionAt B S ⧸ gammaHomogeneousIdealAt (B := B) (S := S)) ≃+*
      GrothendieckAddGroup (gammaIspRingConAt (S := S) hκ hs h00 hsmall).Quotient := by
  rw [← gammaIsp_relationIdeal_principal hκ hs h00 hsmall]
  exact GroupifiedCongruence.quotientEquiv _

end IntegrationInACVF.Section6.FiniteRV
