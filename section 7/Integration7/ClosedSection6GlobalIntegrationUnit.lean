module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalIntegrationProducts
public import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
public import Integration7.ClosedSection6GlobalQuotientAdditiveLift
public import Integration7.ClosedSection6FiniteVFIntegralScissors
public import Integration7.ClosedSection6GammaVFAllAdditivePresentation
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalIntegrationUnit
public import IntegrationSection6.GlobalIntegrationProducts
public import IntegrationSection6.GammaGlobalAdditiveLiftProducts
public import IntegrationSection6.GlobalQuotientAdditiveLift
public import IntegrationSection6.FiniteVFIntegralScissors
public import IntegrationSection6.GammaVFAllAdditivePresentation
public import IntegrationSection6.GammaVFAllFinitePresentation
public import IntegrationSection6.FiniteIntegrationPadding
public import IntegrationSection6.GammaNonzeroResolutions
public import IntegrationSection6.GammaNonzeroQuotientLift
public import IntegrationSection6.GammaNonzeroThroughTransitions
public import IntegrationSection6.GammaIspPadding

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

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
    globalAdditiveIntegrationToSemiring hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
      (PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllUnit B)) = 1 := by
  rw [← gammaNonzeroGlobalAdditiveLiftAt_one hκ hs h00 hreal hB,globalIntegration_lift_value,map_one]

end IntegrationInACVF.Section7.CompletedSection6
