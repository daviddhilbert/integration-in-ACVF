import IntegrationSection6.FamilyConstantProductLifts
import IntegrationSection6.GammaVFAllBilinearProduct
import IntegrationSection6.RVClassBaseChange

/-! Integration of a family multiplied by a constant RV class is the
product of their actual integration classes. Empty families integrate to zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p k : ℕ}

theorem definableFamilyIntegral_constant_product (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : DefinableRVFamily B A) (U : GammaObjectAt B Set.univ k) :
    P.integral A hA (Quotient.mk _ (F.product (DefinableRVFamily.constant U A))) =
      P.integral A hA (Quotient.mk _ F) * P.rvClass U := by
  letI := P.vfSemiring
  let X := gammaFamilyLift A hA F.schema F.finite
  let Y := gammaVFAllFromBounded ⟨gammaLiftVF U.toGamma.toGammaRVObject,
    gammaLiftVF_finite U.toGamma.toGammaRVObject U.object.property⟩
  change P.equivalence (PositiveAdditiveGrothendieck.of _ _) =
    P.equivalence (PositiveAdditiveGrothendieck.of _ X) * P.rvClass U
  rw [← P.equivalence_lift U,← map_mul]
  apply congrArg P.equivalence
  change PositiveAdditiveGrothendieck.of _ _ = gammaVFProductBilinear (PositiveAdditiveGrothendieck.of _ X)
    (PositiveAdditiveGrothendieck.of _ Y)
  exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) (b := gammaVFAllProduct X Y)
    ⟨(gammaFamilyConstantProductIso A hA F.schema U).symm (gammaLogicInput B)⟩).trans
      (gammaVFProductBilinear_class X Y).symm

theorem definableFamilyIntegral_zero (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :
    P.integral A hA (Quotient.mk _ (DefinableRVFamily.constant
      (gammaEmptyAt (B := B) (n := 0) (Set.subset_univ _)) A)) = 0 := by
  letI := P.vfSemiring
  let U := gammaEmptyAt (B := B) (S := Set.univ) (n := 0) (Set.subset_univ _)
  let F := DefinableRVFamily.constant U A
  have he : familyLiftDomain A F.schema = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨u,_,_⟩ := (constantRVSchema_volume U (q.1 ∘ Fin.castAdd 0) q.2 (tupleRV (q.1 ∘ Fin.natAdd p))).mp hq.2
    exact u.property
  have hc : PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaFamilyLift A hA F.schema F.finite) = 0 :=
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) (b := gammaVFAllEmpty B)
      ⟨gammaEmptyMixedIso he rfl⟩).trans (PositiveAdditiveGrothendieck.of_empty _)
  change P.equivalence (PositiveAdditiveGrothendieck.of _ (gammaFamilyLift A hA F.schema F.finite)) = 0
  rw [hc,map_zero]

end IntegrationInACVF.Section6
