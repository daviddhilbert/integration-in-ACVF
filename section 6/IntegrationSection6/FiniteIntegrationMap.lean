import IntegrationSection6.FiniteVFIntegralScissors
import IntegrationSection6.FiniteVFIntegralEmpty
import IntegrationSection6.NativeFiniteQuotientLift

/-! Integration on the actual finite VF[k] scissor monoid, constructed by
descent of the representative-independent values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

def finiteVFIntegralInvariant :
    Invariant (gammaVFFinitePresentation B k) (A := IntegrationTarget hκ hs h00 hreal k) where
  toFun := vfIntegralValue hκ hs h00 hreal FBase
  iso := fun ⟨e⟩ => vfIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 e
  empty := vfIntegralValue_empty hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
  scissor := fun h => vfIntegralValue_scissor hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 h

def integrationAt : KPlus (gammaVFFinitePresentation B k) →+ IntegrationTarget hκ hs h00 hreal k :=
  lift (gammaVFFinitePresentation B k) (finiteVFIntegralInvariant hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58)

theorem integrationAt_class (A : GammaVFFiniteObject B k) :
    integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 (of (gammaVFFinitePresentation B k) A) =
      vfIntegralValue hκ hs h00 hreal FBase A :=
  lift_of _ _ _

theorem integrationAt_lift_class (U : GammaRVFiniteObject B k) :
    integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 (gammaFiniteLiftScissorClass U) =
      rvIntegralClass hκ hs h00 hreal U := by
  rw [gammaFiniteLiftScissorClass,integrationAt_class]
  exact vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 _ U
    (gammaIso_reflexive U.lift U.toGammaRVObject.lift_definable)

end IntegrationInACVF.Section6.FiniteRV
