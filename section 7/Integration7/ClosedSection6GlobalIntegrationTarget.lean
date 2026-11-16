module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaNonzeroIspUnion
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalIntegrationTarget
public import IntegrationSection6.GammaNonzeroIspUnion
public import IntegrationSection6.GammaNonzeroResolutions
public import IntegrationSection6.GammaNonzeroQuotientLift
public import IntegrationSection6.GammaNonzeroThroughTransitions
public import IntegrationSection6.GammaIspPadding

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


abbrev GlobalIntegrationTarget :=
  (gammaNonzeroIspUnionAddCon (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).Quotient

def integrationTargetToGlobal (k : ℕ) : IntegrationTarget hκ hs h00 hreal k →+
    GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB :=
  (gammaIspAddConAt hκ hs h00 hreal).lift
    ((gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'.comp (gammaNonzeroResolutionAt k))
    (by
      intro a b H
      apply (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).eq.mpr
      refine ⟨k,(gammaFiniteWeightAssemblyAt k).symm a,(gammaFiniteWeightAssemblyAt k).symm b,rfl,rfl,?_⟩
      change gammaClassIspAt hκ hs h00 hreal
        (gammaFiniteWeightAssemblyAt k ((gammaFiniteWeightAssemblyAt k).symm a))
        (gammaFiniteWeightAssemblyAt k ((gammaFiniteWeightAssemblyAt k).symm b))
      rwa [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply])

theorem integrationTargetToGlobal_class (U : GammaObjectAt B Set.univ k) :
    integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k (rvIntegralClass hκ hs h00 hreal U.toGamma) =
      (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).mk'
        (gammaNonzeroResolutionAt k (gammaIsoClassAt U)) := rfl

theorem integrationTargetToGlobal_injective (k : ℕ) : Function.Injective
    (integrationTargetToGlobal (B := B) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k) := by
  intro a b he
  obtain ⟨a,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective a
  obtain ⟨b,rfl⟩ := (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).mk'_surjective b
  have H := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).eq.mp he
  have H' := (gammaNonzeroIspUnionAddCon_stage_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k
    ((gammaFiniteWeightAssemblyAt k).symm a) ((gammaFiniteWeightAssemblyAt k).symm b)).mp H
  apply (gammaIspAddConAt hκ hs h00 hreal).eq.mpr
  change gammaClassIspAt hκ hs h00 hreal
    (gammaFiniteWeightAssemblyAt k ((gammaFiniteWeightAssemblyAt k).symm a))
    (gammaFiniteWeightAssemblyAt k ((gammaFiniteWeightAssemblyAt k).symm b)) at H'
  change gammaClassIspAt hκ hs h00 hreal a b
  simpa only [AddEquiv.apply_symm_apply] using H'

end IntegrationInACVF.Section7.CompletedSection6
