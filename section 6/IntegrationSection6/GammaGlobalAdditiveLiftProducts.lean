import IntegrationSection6.GammaGlobalAdditiveLift
import IntegrationSection6.GammaVFAllBilinearProduct
import IntegrationSection6.GammaLiftPadding
import IntegrationSection6.FiniteGammaClassProducts
import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.NativeFiniteQuotientLift
import IntegrationSection6.GammaProductLifts

/-! Actual additive lifting into the global VF semiring and its product law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

variable {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

theorem gammaAllAdditiveLiftClass_product {l : ℕ} (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    gammaAllAdditiveLiftClass (gammaProductAt U V).toGamma =
      gammaVFProductBilinear (gammaAllAdditiveLiftClass U.toGamma) (gammaAllAdditiveLiftClass V.toGamma) := by
  let A := gammaVFAllFromBounded ⟨gammaLiftVF U.toGamma.toGammaRVObject,gammaLiftVF_finite U.toGamma.toGammaRVObject U.object.property⟩
  let C := gammaVFAllFromBounded ⟨gammaLiftVF V.toGamma.toGammaRVObject,gammaLiftVF_finite V.toGamma.toGammaRVObject V.object.property⟩
  exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B)
    (b := gammaVFAllProduct A C) ⟨gammaProductLiftIsoAt U V⟩).trans
      (gammaVFProductBilinear_class A C).symm

variable [hBS : Fact (B.real ⊆ S)]

theorem gammaAllAdditiveLiftClassesAt_product {l : ℕ} (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB (gammaClassMulAt a b) =
      gammaVFProductBilinear (gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB a)
        (gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB b) := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaClassMulAt_class,gammaAllAdditiveLiftClassesAt_class,gammaAllAdditiveLiftClassesAt_class,gammaAllAdditiveLiftClassesAt_class]
  exact gammaAllAdditiveLiftClass_product U V

theorem gammaNonzeroGlobalAdditiveLiftAt_product (a b : GammaNonzeroGradedAt (B := B) (S := S)) :
    gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB (a*b) =
      gammaVFProductBilinear (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB a)
        (gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB b) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [zero_mul,map_zero,AddMonoidHom.zero_apply]
  | of i a =>
    induction b using DirectSum.induction_on with
    | zero => simp only [mul_zero,map_zero]
    | of j b =>
      rw [DirectSum.of_mul_of]
      change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB (DirectSum.of _ (i+j) (gammaNonzeroMulAt a b)) = _
      rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of,DirectSum.toAddMonoid_of,DirectSum.toAddMonoid_of]
      exact gammaAllAdditiveLiftClassesAt_product hκ hs h00 hsmall hB a.val b.val
    | add b c hb hc => simp only [mul_add,map_add,hb,hc]
  | add a c ha hc => simp only [add_mul,map_add,ha,hc,AddMonoidHom.add_apply]

end IntegrationInACVF.Section6.FiniteRV
