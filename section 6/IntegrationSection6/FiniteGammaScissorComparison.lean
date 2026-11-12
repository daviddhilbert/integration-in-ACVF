import IntegrationSection6.FiniteGammaScissorCoproducts
import IntegrationSection6.FiniteGammaIsoClasses

/-! An additive comparison from actual Gamma RV[k] isomorphism classes
to the inherited finite-volume Gamma scissor presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def gammaIsoClassRepresentativeAt (a : GammaIsoClassesAt B S k) : GammaObjectAt B S k :=
  Classical.choose (gammaIsoClassAt_surjective a)

theorem gammaIsoClassRepresentativeAt_class (a : GammaIsoClassesAt B S k) :
    gammaIsoClassAt (gammaIsoClassRepresentativeAt a) = a :=
  Classical.choose_spec (gammaIsoClassAt_surjective a)

def gammaIsoClassScissorValue (a : GammaIsoClassesAt B S k) : KPlus (gammaRVFinitePresentation B k) :=
  gammaFiniteScissorClass (gammaIsoClassRepresentativeAt a).toGamma

theorem gammaIsoClassScissorValue_class (U : GammaObjectAt B S k) :
    gammaIsoClassScissorValue (gammaIsoClassAt U) = gammaFiniteScissorClass U.toGamma := by
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (gammaIsoClassRepresentativeAt_class (gammaIsoClassAt U))
  exact gammaFiniteScissorClass_iso e.toGamma

def gammaIsoClassesToScissors [hBS : Fact (B.real ⊆ S)] :
    GammaIsoClassesAt B S k →+ KPlus (gammaRVFinitePresentation B k) where
  toFun := gammaIsoClassScissorValue
  map_zero' := by
    rw [← gammaIsoClassAt_empty (n := k) hBS.out,gammaIsoClassScissorValue_class]
    exact gammaFiniteScissorClass_empty (gammaEmptyAt (n := k) hBS.out).toGamma (fun u => u.property)
  map_add' a b := by
    obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
    obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
    rw [← gammaIsoClassAt_coprod,gammaIsoClassScissorValue_class,
      gammaIsoClassScissorValue_class,gammaIsoClassScissorValue_class,gammaFiniteScissorClass_coprod]

@[simp] theorem gammaIsoClassesToScissors_class [Fact (B.real ⊆ S)] (U : GammaObjectAt B S k) :
    gammaIsoClassesToScissors (gammaIsoClassAt U) = gammaFiniteScissorClass U.toGamma :=
  gammaIsoClassScissorValue_class U

end IntegrationInACVF.Section6.FiniteRV
