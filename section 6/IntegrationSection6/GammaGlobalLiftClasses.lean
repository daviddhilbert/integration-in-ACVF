import IntegrationSection6.FiniteGammaClassProducts
import IntegrationSection6.GammaVFFiniteToAll
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

def gammaAllLiftClass (U : GammaRVFiniteObject B k) : GammaVFAllKPlus B :=
  PositiveGrothendieck.of (gammaVFAllPositivePresentation B)
    (gammaVFAllFromBounded ⟨gammaLiftVF U.toGammaRVObject,gammaLiftVF_finite U.toGammaRVObject U.finite_volume⟩)

variable [Fact (B.real ⊆ S)]

def gammaAllLiftClassesAt : GammaIsoClassesAt B S k →+ GammaVFAllKPlus B :=
  gammaVFFiniteToAll.comp (nativeGammaLiftAt hκ hs h00 hsmall hB)

theorem gammaAllLiftClassesAt_class (U : GammaObjectAt B S k) :
    gammaAllLiftClassesAt hκ hs h00 hsmall hB (gammaIsoClassAt U) = gammaAllLiftClass U.toGamma := by
  change gammaVFFiniteToAll (nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt U)) = _
  rw [nativeGammaLiftAt_class]
  exact gammaVFFiniteToAll_class _

theorem gammaAllLiftClass_product {l : ℕ} (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    gammaAllLiftClass (gammaProductAt U V).toGamma = gammaAllLiftClass U.toGamma * gammaAllLiftClass V.toGamma := by
  let A := gammaVFAllFromBounded ⟨gammaLiftVF U.toGamma.toGammaRVObject,gammaLiftVF_finite U.toGamma.toGammaRVObject U.object.property⟩
  let C := gammaVFAllFromBounded ⟨gammaLiftVF V.toGamma.toGammaRVObject,gammaLiftVF_finite V.toGamma.toGammaRVObject V.object.property⟩
  exact (PositiveGrothendieck.of_iso (gammaVFAllPositivePresentation B)
    (b := gammaVFAllProduct A C) ⟨gammaProductLiftIsoAt U V⟩).trans
      (PositiveGrothendieck.of_product (gammaVFAllPositivePresentation B) A C)

theorem gammaAllLiftClassesAt_mul {l : ℕ} (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaAllLiftClassesAt hκ hs h00 hsmall hB (gammaClassMulAt a b) =
      gammaAllLiftClassesAt hκ hs h00 hsmall hB a * gammaAllLiftClassesAt hκ hs h00 hsmall hB b := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaClassMulAt_class,gammaAllLiftClassesAt_class,gammaAllLiftClassesAt_class,gammaAllLiftClassesAt_class]
  exact gammaAllLiftClass_product U V

end IntegrationInACVF.Section6.FiniteRV
