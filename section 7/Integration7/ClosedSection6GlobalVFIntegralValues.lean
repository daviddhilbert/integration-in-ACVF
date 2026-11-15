import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6GlobalVFIntegralBounds
import Integration7.ClosedSection6GammaVFAllAdditivePresentation
import Integration7.ClosedSection6GammaVFAllFinitePresentation
import Integration7.ClosedSection6FiniteIntegrationPadding
import Integration7.ClosedSection6GammaNonzeroQuotientLift
import Integration7.ClosedSection6GammaIspPadding
import IntegrationSection6.GlobalVFIntegralValues
import IntegrationSection6.GlobalVFIntegralBounds
import IntegrationSection6.GammaVFAllAdditivePresentation
import IntegrationSection6.GammaVFAllFinitePresentation
import IntegrationSection6.FiniteIntegrationPadding
import IntegrationSection6.GammaNonzeroResolutions
import IntegrationSection6.GammaNonzeroQuotientLift
import IntegrationSection6.GammaNonzeroThroughTransitions
import IntegrationSection6.GammaIspPadding

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


theorem globalVFIntegralAt_iso {j : ℕ} (A : GammaVFFiniteObject B k) (C : GammaVFFiniteObject B j)
    (e : GammaIso B A.val.domain C.val.domain) :
    globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB C := by
  let l := max k j
  have hkl : k ≤ l := le_max_left _ _
  have hjl : j ≤ l := le_max_right _ _
  have H := congrArg (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB l)
    ((vfIntegralValue_iso (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
      (A := gammaVFChangeBound A l hkl) (C := gammaVFChangeBound C l hjl) e)
  exact (globalVFIntegralAt_change_bound hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A l hkl).symm.trans
    (H.trans (globalVFIntegralAt_change_bound hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB C l hjl))

def globalVFAllIntegralValue (A : GammaVFAllFiniteObject B) : GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB :=
  globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFAllBounded A)

theorem globalVFAllIntegralValue_iso {A C : GammaVFAllFiniteObject B} (e : GammaIso B A.domain C.domain) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A =
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB C :=
  globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFAllBounded A) (gammaVFAllBounded C) e

theorem globalVFAllIntegralValue_from_bounded (A : GammaVFFiniteObject B k) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFAllFromBounded A) =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A :=
  globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB _ A
    (gammaIso_reflexive A.val.domain A.val.definable)

theorem globalVFAllIntegralValue_empty :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFAllEmpty B) = 0 := by
  let C := (gammaVFFinitePresentation B 0).empty
  have hC : C.val.domain = ∅ := by
    ext p
    constructor
    · rintro ⟨u,_,_⟩
      exact u.property
    · exact False.elim
  have H := globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB
    (gammaVFAllBounded (gammaVFAllEmpty B)) C (gammaEmptyMixedIso rfl hC)
  exact H.trans (by
    change integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB 0
      ((vfIntegralValue (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase (gammaVFFinitePresentation B 0).empty) = 0
    rw [(vfIntegralValue_empty (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc,map_zero])

end IntegrationInACVF.Section7.CompletedSection6
