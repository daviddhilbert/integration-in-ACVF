import IntegrationSection6.GammaNonzeroResolutions
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

def gammaAllAdditiveLiftClass (U : GammaRVFiniteObject B k) : GammaVFAllAdditiveKPlus B :=
  PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B)
    (gammaVFAllFromBounded ⟨gammaLiftVF U.toGammaRVObject,gammaLiftVF_finite U.toGammaRVObject U.finite_volume⟩)

variable [Fact (B.real ⊆ S)]

def gammaAllAdditiveLiftClassesAt : GammaIsoClassesAt B S k →+ GammaVFAllAdditiveKPlus B :=
  gammaVFFiniteToAllAdditive.comp (nativeGammaLiftAt hκ hs h00 hsmall hB)

theorem gammaAllAdditiveLiftClassesAt_class (U : GammaObjectAt B S k) :
    gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB (gammaIsoClassAt U) = gammaAllAdditiveLiftClass U.toGamma := by
  change gammaVFFiniteToAllAdditive (nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt U)) = _
  rw [nativeGammaLiftAt_class]
  exact gammaVFFiniteToAllAdditive_class _



def gammaNonzeroGlobalAdditiveLiftAt : GammaNonzeroGradedAt (B := B) (S := S) →+ GammaVFAllAdditiveKPlus B :=
  DirectSum.toAddMonoid (fun k => (gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB).comp (gammaNonzeroClassSubmonoidAt k).subtype)

theorem gammaAllAdditiveLiftClass_padding (U : GammaObjectAt B S k) :
    gammaAllAdditiveLiftClass (gammaPadAt U).toGamma = gammaAllAdditiveLiftClass U.toGamma :=
  (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨gammaLiftPaddingIsoAt U⟩).symm

theorem gammaAllAdditiveLiftClassesAt_padding (a : GammaIsoClassesAt B S k) :
    gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB (gammaPaddingClassesAt a) = gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB a := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  rw [gammaPaddingClassesAt_class,gammaAllAdditiveLiftClassesAt_class,gammaAllAdditiveLiftClassesAt_class]
  exact gammaAllAdditiveLiftClass_padding U

theorem gammaNonzeroGlobalAdditiveLiftAt_through (k : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k) :
    gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB (gammaThroughToGradedAt k a) =
      gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB (gammaFiniteWeightAssemblyAt k a) := by
  induction k with
  | zero =>
    change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB
      (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 0 a) = gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB a.val
    rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
    rfl
  | succ n ih =>
    change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB
      (gammaThroughToGradedAt n a.1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a.2) = _
    rw [map_add,ih,gammaFiniteWeightAssemblyAt_succ,map_add,gammaAllAdditiveLiftClassesAt_padding]
    congr 1
    rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
    rfl

theorem gammaNonzeroGlobalAdditiveLiftAt_resolution (k : ℕ) (a : GammaIsoClassesAt B S k) :
    gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB (gammaNonzeroResolutionAt k a) =
      gammaAllAdditiveLiftClassesAt hκ hs h00 hsmall hB a := by
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hsmall hB
    (gammaThroughToGradedAt k ((gammaFiniteWeightAssemblyAt k).symm a)) = _
  rw [gammaNonzeroGlobalAdditiveLiftAt_through,AddEquiv.apply_symm_apply]

end IntegrationInACVF.Section6.FiniteRV
