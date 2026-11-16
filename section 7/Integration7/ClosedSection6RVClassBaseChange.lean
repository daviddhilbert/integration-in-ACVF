module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ContextRVClasses
public import Integration7.ClosedSection6GammaGlobalAdditiveLift
public import IntegrationSection6.RVClassBaseChange
public import IntegrationSection6.ContextRVClasses
public import IntegrationSection6.GammaGradedResolution
public import IntegrationSection6.GammaGlobalAdditiveLift

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
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def GammaObjectAt.changeBase (U : GammaObjectAt B Set.univ k) (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    GammaObjectAt C Set.univ k where
  object := U.object
  real_contains := Set.subset_univ _
  domain_graph := U.domain_graph.mono hr hg
  volume_graph := U.volume_graph.mono hr hg

theorem IntegrationContext.equivalence_lift (P : IntegrationContext B κ hs) (U : GammaObjectAt B Set.univ k) :
    letI := P.vfSemiring
    P.equivalence (gammaAllAdditiveLiftClass U.toGamma) = P.rvClass U :=
  theorem_6_19_lift_finite P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.canonical P.generated U.toGamma

theorem IntegrationContext.rvClass_unit (P : IntegrationContext B κ hs) :
    P.rvClass (gammaUnitAt (Set.subset_univ _)) = 1 := by
  change (gammaNonzeroIspUnionRingCon P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.canonical P.generated).mk'
      (gammaNonzeroResolutionAt 0 (gammaIsoClassAt (gammaUnitAt (Set.subset_univ _)))) = 1
  have h : gammaNonzeroResolutionAt (B := B) (S := Set.univ) 0 (gammaIsoClassAt (gammaUnitAt (Set.subset_univ _))) = 1 :=
    gammaNonzeroResolutionAt_pure 0 (GradedMonoid.GOne.one : GammaNonzeroClassesAt (B := B) (S := Set.univ) 0)
  rw [h,map_one]

theorem IntegrationContext.scalarMap_rvClass (P : IntegrationContext B κ hs) {p : ℕ}
    (x : Fin p → VF (M := M)) (U : GammaObjectAt B Set.univ k)
    (hr : B.real ⊆ (vfParameterCoefficientBase B x).real)
    (hg : B.gamma ⊆ (vfParameterCoefficientBase B x).gamma) :
    P.scalarMap x (P.rvClass U) = (P.atVF x).rvClass (U.changeBase hr hg) := by
  letI := P.vfSemiring
  letI := (P.atVF x).vfSemiring
  change (P.atVF x).equivalence
    (gammaVFBaseChange hr hg (P.equivalence.symm (P.rvClass U))) = _
  rw [← P.equivalence_lift U,RingEquiv.symm_apply_apply]
  rw [gammaAllAdditiveLiftClass,gammaVFBaseChange_class]
  exact (P.atVF x).equivalence_lift (U.changeBase hr hg)

end IntegrationInACVF.Section7.CompletedSection6
