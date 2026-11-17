module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GlobalIntegrationTarget
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import Integration7.ClosedSection6FiniteIntegrationPadding
public import Integration7.ClosedSection6GammaNonzeroQuotientLift
public import Integration7.ClosedSection6GammaIspPadding
public import IntegrationSection6.GlobalVFIntegralBounds
public import IntegrationSection6.GlobalIntegrationTarget
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


def gammaVFRaise (A : GammaVFFiniteObject B k) : GammaVFFiniteObject B (k+1) :=
  ⟨⟨A.val.arity,A.val.domain,A.val.definable,gammaDimension_mono A.val.dimension (Nat.le_succ k)⟩,A.property⟩

def globalVFIntegralAt (A : GammaVFFiniteObject B k) : GlobalIntegrationTarget hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB :=
  integrationTargetToGlobal hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB k
    ((vfIntegralValue (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase A)

theorem globalVFIntegralAt_raise (A : GammaVFFiniteObject B k) :
    globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFRaise A) =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A := by
  let R := (finiteVFLiftRepresentative (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase A
  let U := gammaUniversalObject R.1
  let e : GammaIso B A.val.domain U.toGamma.lift := R.2
  let f : GammaIso B (gammaVFRaise A).val.domain (gammaPadAt U).toGamma.lift := e.trans (gammaLogicInput B) (gammaLiftPaddingIsoAt U)
  have hU := (vfIntegralValue_of_lift_representation (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc A U.toGamma e
  have hV := (vfIntegralValue_of_lift_representation (hgen := ⟨hB⟩)) hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc (gammaVFRaise A) (gammaPadAt U).toGamma f
  unfold globalVFIntegralAt
  rw [hV,hU,integrationTargetToGlobal_class,integrationTargetToGlobal_class]
  rw [← gammaPaddingClassesAt_class,gammaNonzeroResolutionAt_padding]

def gammaVFChangeBound (A : GammaVFFiniteObject B k) (j : ℕ) (hj : k ≤ j) : GammaVFFiniteObject B j :=
  ⟨⟨A.val.arity,A.val.domain,A.val.definable,gammaDimension_mono A.val.dimension hj⟩,A.property⟩

theorem globalVFIntegralAt_change_bound (A : GammaVFFiniteObject B k) (j : ℕ) (hj : k ≤ j) :
    globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFChangeBound A j hj) =
      globalVFIntegralAt hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB A := by
  induction j,hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    exact (globalVFIntegralAt_raise hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc hB (gammaVFChangeBound A j hj)).trans ih

end IntegrationInACVF.Section7.CompletedSection6
