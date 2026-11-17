module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalAdditiveIntegrationEquivalence
public import Integration7.ClosedSection6GammaGlobalAdditiveLiftProducts
public import Integration7.ClosedSection6GlobalQuotientAdditiveLift
public import Integration7.ClosedSection6FiniteVFIntegralScissors
public import Integration7.ClosedSection6GammaVFAllAdditivePresentation
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GammaNonzeroIspSemiring
public import IntegrationSection6.GlobalAdditiveIntegrationEquivalence
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


theorem gammaNonzeroIspUnionAddCon_eq_lift_kernel :
    gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB =
      AddCon.ker (gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ hs h00 hreal hB) := by
  apply le_antisymm
  · exact gammaGlobalAdditiveLift_respects_union hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  · intro a b H
    apply (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).eq.mp
    apply (globalAdditiveIntegrationEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).symm.injective
    exact H

def gammaNonzeroIspUnionRingCon : RingCon (GammaNonzeroGradedAt (B := B) (S := Set.univ)) where
  r := gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
  iseqv := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).iseqv
  add' := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB).add
  mul' := by
    intro a b c d hab hcd
    have he := gammaNonzeroIspUnionAddCon_eq_lift_kernel hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    rw [he] at hab hcd ⊢
    change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (a*c) = gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (b*d)
    rw [gammaNonzeroGlobalAdditiveLiftAt_product,gammaNonzeroGlobalAdditiveLiftAt_product]
    exact congrArg₂ (fun x y => gammaVFProductBilinear x y) hab hcd

theorem gammaNonzeroIspRingCon_eq_union : gammaNonzeroIspRingCon (B := B) hκ hs h00 hreal =
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB := by
  apply le_antisymm
  · apply RingCon.ringConGen_le.mpr
    intro a b H
    exact H
  · intro a b H
    exact RingConGen.Rel.of a b H

end IntegrationInACVF.Section7.CompletedSection6
