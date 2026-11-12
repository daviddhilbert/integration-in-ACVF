import IntegrationSection6.GlobalAdditiveIntegrationEquivalence
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

theorem gammaNonzeroIspUnionAddCon_eq_lift_kernel :
    gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB =
      AddCon.ker (gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ hs h00 hreal hB) := by
  apply le_antisymm
  · exact gammaGlobalAdditiveLift_respects_union hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  · intro a b H
    apply (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).eq.mp
    apply (globalAdditiveIntegrationEquiv hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).symm.injective
    exact H

def gammaNonzeroIspUnionRingCon : RingCon (GammaNonzeroGradedAt (B := B) (S := Set.univ)) where
  r := gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
  iseqv := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).iseqv
  add' := (gammaNonzeroIspUnionAddCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB).add
  mul' := by
    intro a b c d hab hcd
    have he := gammaNonzeroIspUnionAddCon_eq_lift_kernel hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    rw [he] at hab hcd ⊢
    change gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (a*c) = gammaNonzeroGlobalAdditiveLiftAt hκ hs h00 hreal hB (b*d)
    rw [gammaNonzeroGlobalAdditiveLiftAt_product,gammaNonzeroGlobalAdditiveLiftAt_product]
    exact congrArg₂ (fun x y => gammaVFProductBilinear x y) hab hcd

theorem gammaNonzeroIspRingCon_eq_union : gammaNonzeroIspRingCon (B := B) hκ hs h00 hreal =
    gammaNonzeroIspUnionRingCon hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB := by
  apply le_antisymm
  · apply RingCon.ringConGen_le.mpr
    intro a b H
    exact H
  · intro a b H
    exact RingConGen.Rel.of a b H

end IntegrationInACVF.Section6.FiniteRV
