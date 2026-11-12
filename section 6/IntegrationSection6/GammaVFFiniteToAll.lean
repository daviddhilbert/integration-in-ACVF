import IntegrationSection6.GammaVFAllFinitePresentation
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

def gammaVFFiniteToAllInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFFinitePresentation B k)
    (A := GammaVFAllKPlus B) where
  toFun A := PositiveGrothendieck.of (gammaVFAllPositivePresentation B) (gammaVFAllFromBounded A)
  iso h := PositiveGrothendieck.of_iso (gammaVFAllPositivePresentation B) h
  empty := by
    have hEmpty : (gammaVFFinitePresentation B k).empty.val.domain = ∅ := by
      ext p
      constructor
      · rintro ⟨u,_,_⟩
        exact u.property
      · exact False.elim
    exact (PositiveGrothendieck.of_iso (gammaVFAllPositivePresentation B)
      (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso hEmpty rfl⟩).trans
      (PositiveGrothendieck.of_empty (gammaVFAllPositivePresentation B))
  scissor h := PositiveGrothendieck.of_scissor (gammaVFAllPositivePresentation B) h

def gammaVFFiniteToAll : PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) →+ GammaVFAllKPlus B :=
  PositiveAdditiveGrothendieck.lift _ gammaVFFiniteToAllInvariant

theorem gammaVFFiniteToAll_class (A : GammaVFFiniteObject B k) :
    gammaVFFiniteToAll (PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A) =
      PositiveGrothendieck.of (gammaVFAllPositivePresentation B) (gammaVFAllFromBounded A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

end IntegrationInACVF.Section6.FiniteRV
