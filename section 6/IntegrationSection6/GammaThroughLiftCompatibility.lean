import IntegrationSection6.GammaNonzeroGlobalLift
import IntegrationSection6.GammaNonzeroResolutions
import IntegrationSection6.GammaLiftPadding

/-! Finite weight assembly and global semiring lifting commute. -/
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

theorem gammaAllLiftClass_padding (U : GammaObjectAt B S k) :
    gammaAllLiftClass (gammaPadAt U).toGamma = gammaAllLiftClass U.toGamma :=
  (PositiveGrothendieck.of_iso (gammaVFAllPositivePresentation B) ⟨gammaLiftPaddingIsoAt U⟩).symm

variable [hBS : Fact (B.real ⊆ S)]

theorem gammaAllLiftClassesAt_padding (a : GammaIsoClassesAt B S k) :
    gammaAllLiftClassesAt hκ hs h00 hsmall hB (gammaPaddingClassesAt a) = gammaAllLiftClassesAt hκ hs h00 hsmall hB a := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  rw [gammaPaddingClassesAt_class,gammaAllLiftClassesAt_class,gammaAllLiftClassesAt_class]
  exact gammaAllLiftClass_padding U

theorem gammaNonzeroGlobalLiftAt_through (k : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k) :
    gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB (gammaThroughToGradedAt k a) =
      gammaAllLiftClassesAt hκ hs h00 hsmall hB (gammaFiniteWeightAssemblyAt k a) := by
  induction k with
  | zero =>
    change gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB
      (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 0 a) = gammaAllLiftClassesAt hκ hs h00 hsmall hB a.val
    rw [gammaNonzeroGlobalLiftAt,DirectSum.toSemiring_of]
    rfl
  | succ n ih =>
    change gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB
      (gammaThroughToGradedAt n a.1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a.2) = _
    rw [map_add,ih,gammaFiniteWeightAssemblyAt_succ,map_add,gammaAllLiftClassesAt_padding]
    congr 1
    rw [gammaNonzeroGlobalLiftAt,DirectSum.toSemiring_of]
    rfl

theorem gammaNonzeroGlobalLiftAt_resolution (k : ℕ) (a : GammaIsoClassesAt B S k) :
    gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB (gammaNonzeroResolutionAt k a) =
      gammaAllLiftClassesAt hκ hs h00 hsmall hB a := by
  change gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB
    (gammaThroughToGradedAt k ((gammaFiniteWeightAssemblyAt k).symm a)) = _
  rw [gammaNonzeroGlobalLiftAt_through,AddEquiv.apply_symm_apply]

end IntegrationInACVF.Section6.FiniteRV
