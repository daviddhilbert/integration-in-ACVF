import IntegrationSection6.GammaVFAllBilinearProduct

/-! Base extension on the actual finite VF scissor monoids preserves
addition, Cartesian product and the singleton. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma)

def gammaVFAllChangeBase (A : GammaVFAllFiniteObject B) : GammaVFAllFiniteObject C :=
  ⟨A.arity,A.domain,A.definable.mono hr hg,A.finiteFibres⟩

def gammaVFBaseChangeInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFAllAdditivePresentation B)
    (A := GammaVFAllAdditiveKPlus C) where
  toFun A := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation C) (gammaVFAllChangeBase hr hg A)
  iso := fun ⟨e⟩ => PositiveAdditiveGrothendieck.of_iso _ ⟨⟨e.equiv,e.graph.mono hr hg⟩⟩
  empty := PositiveAdditiveGrothendieck.of_empty (gammaVFAllAdditivePresentation C)
  scissor := fun h => PositiveAdditiveGrothendieck.of_scissor (gammaVFAllAdditivePresentation C) h

def gammaVFBaseChange : GammaVFAllAdditiveKPlus B →+ GammaVFAllAdditiveKPlus C :=
  PositiveAdditiveGrothendieck.lift _ (gammaVFBaseChangeInvariant hr hg)

theorem gammaVFBaseChange_class (A : GammaVFAllFiniteObject B) :
    gammaVFBaseChange hr hg (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation C) (gammaVFAllChangeBase hr hg A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

theorem gammaVFBaseChange_product (a b : GammaVFAllAdditiveKPlus B) :
    gammaVFBaseChange hr hg (gammaVFProductBilinear a b) =
      gammaVFProductBilinear (gammaVFBaseChange hr hg a) (gammaVFBaseChange hr hg b) := by
  let F := gammaVFBaseChange hr hg
  have hgen (A : GammaVFAllFiniteObject B) :
      F.comp (gammaVFProductBilinear (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A)) =
        (gammaVFProductBilinear (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation C)
          (gammaVFAllChangeBase hr hg A))).comp F := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro R
    change gammaVFBaseChange hr hg (gammaVFProductBilinear (PositiveAdditiveGrothendieck.of _ A)
      (PositiveAdditiveGrothendieck.of _ R)) = gammaVFProductBilinear
        (PositiveAdditiveGrothendieck.of _ (gammaVFAllChangeBase hr hg A))
        (gammaVFBaseChange hr hg (PositiveAdditiveGrothendieck.of _ R))
    rw [gammaVFProductBilinear_class,gammaVFBaseChange_class,gammaVFBaseChange_class,gammaVFProductBilinear_class]
    rfl
  have he : F.comp (gammaVFProductBilinear.flip b) = (gammaVFProductBilinear.flip (F b)).comp F := by
    apply PositiveAdditiveGrothendieck.hom_ext
    intro A
    change F (gammaVFProductBilinear (PositiveAdditiveGrothendieck.of _ A) b) =
      gammaVFProductBilinear (F (PositiveAdditiveGrothendieck.of _ A)) (F b)
    rw [gammaVFBaseChange_class]
    exact DFunLike.congr_fun (hgen A) b
  exact DFunLike.congr_fun he a

theorem gammaVFBaseChange_unit :
    gammaVFBaseChange hr hg (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation C) (gammaVFAllUnit C) :=
  gammaVFBaseChange_class hr hg _

end IntegrationInACVF.Section6.FiniteRV
