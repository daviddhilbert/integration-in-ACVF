import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.GammaVFAllProductScissors
import IntegrationSection6.GammaMixedProductIsomorphisms
import IntegrationSection6.GammaMixedEmptyIsomorphisms
import Section5.GammaSurjectivity
import Section7.GammaScissors

/-! The representative-independent integration value of an actual VF[k]
object with finite RV fibres. Representatives come from the checked5.7
surjectivity theorem; independence uses the proved6.17 kernel implication. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaVFProductRightInvariant (R : GammaVFAllFiniteObject B) :
    PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B) (A := GammaVFAllAdditiveKPlus B) where
  toFun A := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllProduct A R)
  iso := fun ⟨e⟩ => PositiveAdditiveGrothendieck.of_iso _ ⟨gammaMixedProductIso e (gammaIso_reflexive R.domain R.definable)⟩
  empty := by
    have he : (gammaVFAllProduct (gammaVFAllEmpty B) R).domain = ∅ := by
      ext p
      constructor
      · intro h; exact h.1.elim
      · exact False.elim
    exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B)
      (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso he rfl⟩).trans (PositiveAdditiveGrothendieck.of_empty _)
  scissor := fun h => PositiveAdditiveGrothendieck.of_scissor _ (gammaVFAllScissor_product_right h R)

def gammaVFProductRightHom (R : GammaVFAllFiniteObject B) : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B :=
  PositiveAdditiveGrothendieck.lift _ (gammaVFProductRightInvariant R)

theorem gammaVFProductRightHom_class (A R : GammaVFAllFiniteObject B) :
    gammaVFProductRightHom R (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllProduct A R) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

def gammaVFProductLeftInvariant (A : GammaVFAllFiniteObject B) :
    PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B) (A := GammaVFAllAdditiveKPlus B) where
  toFun R := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllProduct A R)
  iso := fun ⟨e⟩ => PositiveAdditiveGrothendieck.of_iso _ ⟨gammaMixedProductIso (gammaIso_reflexive A.domain A.definable) e⟩
  empty := by
    have he : (gammaVFAllProduct A (gammaVFAllEmpty B)).domain = ∅ := by
      ext p
      constructor
      · intro h; exact h.2.elim
      · exact False.elim
    exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B)
      (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso he rfl⟩).trans (PositiveAdditiveGrothendieck.of_empty _)
  scissor := fun h => PositiveAdditiveGrothendieck.of_scissor _ (gammaVFAllScissor_product_left h A)

def gammaVFProductLeftHom (A : GammaVFAllFiniteObject B) : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B :=
  PositiveAdditiveGrothendieck.lift _ (gammaVFProductLeftInvariant A)

theorem gammaVFProductLeftHom_class (A R : GammaVFAllFiniteObject B) :
    gammaVFProductLeftHom A (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) R) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllProduct A R) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

def gammaVFProductBilinearInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B)
    (A := GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B) where
  toFun := gammaVFProductRightHom
  iso := by
    rintro R T ⟨e⟩
    apply PositiveAdditiveGrothendieck.hom_ext
    intro A
    rw [gammaVFProductRightHom_class,gammaVFProductRightHom_class]
    exact PositiveAdditiveGrothendieck.of_iso _ ⟨gammaMixedProductIso (gammaIso_reflexive A.domain A.definable) e⟩
  empty := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro A
    change gammaVFProductRightHom (gammaVFAllEmpty B) (PositiveAdditiveGrothendieck.of _ A) = 0
    rw [gammaVFProductRightHom_class,← gammaVFProductLeftHom_class]
    change gammaVFProductLeftHom A (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllAdditivePresentation B).empty) = 0
    rw [PositiveAdditiveGrothendieck.of_empty,map_zero]
  scissor := by
    intro A C D E h
    apply PositiveAdditiveGrothendieck.hom_ext
    intro R
    simp only [AddMonoidHom.add_apply,gammaVFProductRightHom_class]
    exact PositiveAdditiveGrothendieck.of_scissor _ (gammaVFAllScissor_product_left h R)

def gammaVFProductBilinear : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus B :=
  (PositiveAdditiveGrothendieck.lift _ gammaVFProductBilinearInvariant).flip

theorem gammaVFProductBilinear_class (A R : GammaVFAllFiniteObject B) :
    gammaVFProductBilinear (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A)
      (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) R) =
        PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllProduct A R) := by
  change (PositiveAdditiveGrothendieck.lift _ gammaVFProductBilinearInvariant
    (PositiveAdditiveGrothendieck.of _ R)) (PositiveAdditiveGrothendieck.of _ A) = _
  rw [PositiveAdditiveGrothendieck.lift_of]
  exact gammaVFProductRightHom_class A R

end IntegrationInACVF.Section6.FiniteRV
