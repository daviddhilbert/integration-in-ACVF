import IntegrationSection6.GammaMixedEmptyIsomorphisms
import IntegrationSection6.GammaVFAllFinitePresentation
import IntegrationSection6.GammaMixedProducts
import Section4.PositivePresentation
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

def gammaVFAllAdditivePresentation (B : Base (M := M)) : PositiveAdditiveGrothendieck.Presentation (GammaVFAllFiniteObject B) where
  iso A C := Nonempty (GammaIso B A.domain C.domain)
  empty := gammaVFAllEmpty B
  scissor := GammaVFAllScissor

abbrev GammaVFAllAdditiveKPlus (B : Base (M := M)) := PositiveAdditiveGrothendieck.KPlus (gammaVFAllAdditivePresentation B)

def gammaVFFiniteToAllAdditiveInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFFinitePresentation B k)
    (A := GammaVFAllAdditiveKPlus B) where
  toFun A := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllFromBounded A)
  iso h := PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) h
  empty := by
    have hEmpty : (gammaVFFinitePresentation B k).empty.val.domain = ∅ := by
      ext p
      constructor
      · rintro ⟨u,_,_⟩
        exact u.property
      · exact False.elim
    exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B)
      (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso hEmpty rfl⟩).trans
      (PositiveAdditiveGrothendieck.of_empty (gammaVFAllAdditivePresentation B))
  scissor h := PositiveAdditiveGrothendieck.of_scissor (gammaVFAllAdditivePresentation B) h

def gammaVFFiniteToAllAdditive : PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) →+ GammaVFAllAdditiveKPlus B :=
  PositiveAdditiveGrothendieck.lift _ gammaVFFiniteToAllAdditiveInvariant

theorem gammaVFFiniteToAllAdditive_class (A : GammaVFFiniteObject B k) :
    gammaVFFiniteToAllAdditive (PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllFromBounded A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

end IntegrationInACVF.Section6.FiniteRV
