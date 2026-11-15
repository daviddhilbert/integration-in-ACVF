import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6FiniteVFIntegralScissors
import Integration7.ClosedSection6FiniteVFIntegralEmpty
import IntegrationSection6.FiniteIntegrationMap
import IntegrationSection6.FiniteVFIntegralScissors
import IntegrationSection6.FiniteVFIntegralEmpty
import IntegrationSection6.NativeFiniteQuotientLift

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
variable {B : Base (M := M)} {k : ℕ}
variable [hgen : Fact (VFGammaGeneratedBase B)]

local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

def finiteVFIntegralInvariant :
    Invariant (gammaVFFinitePresentation B k) (A := IntegrationTarget hκ hs h00 hreal k) where
  toFun := vfIntegralValue hκ hs h00 hreal FBase
  iso := fun ⟨e⟩ => vfIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc e
  empty := vfIntegralValue_empty hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
  scissor := fun h => vfIntegralValue_scissor hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc h

def integrationAt : KPlus (gammaVFFinitePresentation B k) →+ IntegrationTarget hκ hs h00 hreal k :=
  lift (gammaVFFinitePresentation B k) (finiteVFIntegralInvariant hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc)

theorem integrationAt_class (A : GammaVFFiniteObject B k) :
    integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc (of (gammaVFFinitePresentation B k) A) =
      vfIntegralValue hκ hs h00 hreal FBase A :=
  lift_of _ _ _

theorem integrationAt_lift_class (U : GammaRVFiniteObject B k) :
    integrationAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc (gammaFiniteLiftScissorClass U) =
      rvIntegralClass hκ hs h00 hreal U := by
  rw [gammaFiniteLiftScissorClass,integrationAt_class]
  exact vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc _ U
    (gammaIso_reflexive U.lift U.toGammaRVObject.lift_definable)

end IntegrationInACVF.Section7.CompletedSection6
