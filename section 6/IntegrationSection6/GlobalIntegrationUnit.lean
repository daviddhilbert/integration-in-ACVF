import IntegrationSection6.GlobalIntegrationProducts
import IntegrationSection6.GammaGlobalAdditiveLiftProducts
import IntegrationSection6.GlobalQuotientAdditiveLift
import IntegrationSection6.FiniteVFIntegralScissors
import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.GammaVFAllFinitePresentation
import IntegrationSection6.FiniteIntegrationPadding
import IntegrationSection6.GammaNonzeroResolutions
import IntegrationSection6.GammaNonzeroQuotientLift
import IntegrationSection6.GammaNonzeroThroughTransitions
import IntegrationSection6.GammaIspPadding

/-! The nonzero-coordinate filtered form of fixed-degree integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

variable (hB : VFGammaGeneratedBase B)

variable {S : Set M}

theorem gammaAllAdditiveLiftClass_unit (hBS : B.real ⊆ S) :
    gammaAllAdditiveLiftClass (gammaUnitAt hBS).toGamma = PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B) := by
  have hU : (gammaUnitAt hBS).toGamma.lift = (Set.univ : Set (Point (M := M) 0 0)) := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact ⟨⟨Fin.elim0,Set.mem_univ _⟩,(by funext i; exact i.elim0),(by funext i; exact i.elim0)⟩
  let e := (gammaIso_reflexive (gammaVFAllUnit B).domain (gammaVFAllUnit B).definable).congr hU.symm rfl
  exact PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e⟩

theorem gammaNonzeroGlobalAdditiveLiftAt_one :
    gammaNonzeroGlobalAdditiveLiftAt (B := B) (S := Set.univ) hκ hs h00 hreal hB 1 =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B) := by
  change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB
    (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 0 GradedMonoid.GOne.one) = _
  rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
  change gammaAllAdditiveLiftClassesAt hκ hs h00 hreal hB (gammaIsoClassAt (gammaUnitAt (Set.subset_univ _))) = _
  rw [gammaAllAdditiveLiftClassesAt_class]
  exact gammaAllAdditiveLiftClass_unit (Set.subset_univ _)

theorem globalIntegration_one :
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
      (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) = 1 := by
  rw [← gammaNonzeroGlobalAdditiveLiftAt_one hκ hs h00 hreal hB,globalIntegration_lift_value,map_one]

end IntegrationInACVF.Section6.FiniteRV
