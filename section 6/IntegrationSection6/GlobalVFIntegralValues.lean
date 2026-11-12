import IntegrationSection6.GlobalVFIntegralBounds
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

theorem globalVFIntegralAt_iso {j : ℕ} (A : GammaVFFiniteObject B k) (C : GammaVFFiniteObject B j)
    (e : GammaIso B A.val.domain C.val.domain) :
    globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB C := by
  let l := max k j
  have hkl : k ≤ l := le_max_left _ _
  have hjl : j ≤ l := le_max_right _ _
  have H := congrArg (integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB l)
    (vfIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
      (A := gammaVFChangeBound A l hkl) (C := gammaVFChangeBound C l hjl) e)
  exact (globalVFIntegralAt_change_bound hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A l hkl).symm.trans
    (H.trans (globalVFIntegralAt_change_bound hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB C l hjl))

def globalVFAllIntegralValue (A : GammaVFAllFiniteObject B) : GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB :=
  globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaVFAllBounded A)

theorem globalVFAllIntegralValue_iso {A C : GammaVFAllFiniteObject B} (e : GammaIso B A.domain C.domain) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A =
      globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB C :=
  globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaVFAllBounded A) (gammaVFAllBounded C) e

theorem globalVFAllIntegralValue_from_bounded (A : GammaVFFiniteObject B k) :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaVFAllFromBounded A) =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB A :=
  globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB _ A
    (gammaIso_reflexive A.val.domain A.val.definable)

theorem globalVFAllIntegralValue_empty :
    globalVFAllIntegralValue hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB (gammaVFAllEmpty B) = 0 := by
  let C := (gammaVFFinitePresentation B 0).empty
  have hC : C.val.domain = ∅ := by
    ext p
    constructor
    · rintro ⟨u,_,_⟩
      exact u.property
    · exact False.elim
  have H := globalVFIntegralAt_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB
    (gammaVFAllBounded (gammaVFAllEmpty B)) C (gammaEmptyMixedIso rfl hC)
  exact H.trans (by
    change integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB 0
      (vfIntegralValue hκ hs h00 hreal FBase (gammaVFFinitePresentation B 0).empty) = 0
    rw [vfIntegralValue_empty hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58,map_zero])

end IntegrationInACVF.Section6.FiniteRV
