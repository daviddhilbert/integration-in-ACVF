import IntegrationSection6.FamilyCoproductLifts
import IntegrationSection6.DefinableFamilyOperations

/-! Integration preserves actual coproduct addition of total family
lifts, including sums whose representatives initially have different degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a b k : ℕ}

theorem gammaFamilyLift_coprod_class (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val))
    (hG : ∀ x : A, G.finiteRow (fun j => (x.val.1 j).val)) :
    PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B)
      (gammaFamilyLift A hA (F.coprodFormula G)
        (fun x => F.finiteRow_coprod G _ (fun j => (x.val.1 j).property) (hF x) (hG x))) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaFamilyLift A hA F hF) +
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaFamilyLift A hA G hG) := by
  let U := gammaFamilyLift A hA F hF
  let V := gammaFamilyLift A hA G hG
  let e := gammaIso_leftTag U.domain U.definable b
  let f := gammaIso_rightTag V.domain V.definable a
  have hL := e.target_definable (gammaLogicInput B)
  have hR := f.target_definable (gammaLogicInput B)
  let fL := taggedLeftSet_finite U.domain U.finiteFibres (r := b)
  let fR := taggedRightSet_finite V.domain V.finiteFibres (m := a)
  let W : GammaVFAllFiniteObject B := ⟨(p+k,1+(a+b)),taggedLeftSet U.domain b ∪ taggedRightSet V.domain a,
    (gammaLogicInput B).union hL hR,fun x => (fL x).union (fR x)⟩
  have hc : PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B)
      (gammaFamilyLift A hA (F.coprodFormula G)
        (fun x => F.finiteRow_coprod G _ (fun j => (x.val.1 j).property) (hF x) (hG x))) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) W :=
    PositiveAdditiveGrothendieck.of_iso _ ⟨(gammaIso_reflexive W.domain W.definable).congr
      (familyLiftDomain_coprod A F G).symm rfl⟩
  refine hc.trans ((gammaVFAll_disjoint_union _ _ hL hR fL fR (tagged_sets_disjoint U.domain V.domain)).trans ?_)
  exact congrArg₂ (· + ·)
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e.symm (gammaLogicInput B)⟩)
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨f.symm (gammaLogicInput B)⟩)

theorem familyIntegralValue_coprod (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (hF : ∀ x : A, F.finiteRow (fun j => (x.val.1 j).val))
    (hG : ∀ x : A, G.finiteRow (fun j => (x.val.1 j).val)) :
    familyIntegralValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order A hA (F.coprodFormula G)
          (fun x => F.finiteRow_coprod G _ (fun j => (x.val.1 j).property) (hF x) (hG x)) =
      familyIntegralValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order A hA F hF +
      familyIntegralValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order A hA G hG := by
  exact (congrArg (globalAdditiveIntegrationToSemiring P.countable_le hs P.characteristic P.real_small P.field_base
    P.gamma_small P.value P.value_mem P.value_large P.section5_two_order P.generated)
    (gammaFamilyLift_coprod_class A hA F G hF hG)).trans (map_add _ _ _)

theorem definableFamilyIntegral_raiseTo (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A)
    (j : ℕ) (hj : F.degree ≤ j) :
    P.integral A hA (Quotient.mk _ (F.raiseTo j hj)) = P.integral A hA (Quotient.mk _ F) := by
  apply congrArg (P.integral A hA)
  exact Quotient.sound (fun x => definableFamilyValue_raiseTo P F j hj x)

theorem definableFamilyIntegral_add (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) (F G : DefinableRVFamily B A) :
    P.integral A hA (Quotient.mk _ (F.add G)) = P.integral A hA (Quotient.mk _ F) + P.integral A hA (Quotient.mk _ G) := by
  exact (familyIntegralValue_coprod P A hA _ _ _ _).trans
    (congrArg₂ (· + ·) (definableFamilyIntegral_raiseTo P A hA F _ _) (definableFamilyIntegral_raiseTo P A hA G _ _))

end IntegrationInACVF.Section6
