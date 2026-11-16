module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6FiniteVFIntegralValues
public import Integration7.ClosedSection6GammaVFFiniteRestrictions
public import IntegrationSection6.FiniteVFIntegralEmpty
public import IntegrationSection6.FiniteGammaEmptyIsomorphisms
public import IntegrationSection6.FiniteVFIntegralValues
public import IntegrationSection6.GammaVFFiniteRestrictions
public import IntegrationSection6.GammaObjectPresentationIsomorphisms

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
variable {B : Base (M := M)} {k : ℕ}
variable [hgen : Fact (VFGammaGeneratedBase B)]

local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

include hgamma δ hδ hδ1 hc in
theorem vfIntegralValue_empty :
    vfIntegralValue hκ hs h00 hreal FBase (gammaVFFinitePresentation B k).empty = 0 := by
  let P := gammaRVFinitePresentation B k
  let U : GammaRVFiniteObject B k := { toGammaRVObject := P.empty.val, finite_volume := P.empty.property }
  have h := vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
    (gammaVFFinitePresentation B k).empty U (gammaIso_reflexive U.lift U.toGammaRVObject.lift_definable)
  rw [h]
  let V := gammaUniversalObject U
  have hV : carrier (rvObjectDomain V.object.obj) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hu
  have he := gammaEmptyIsoAt V hV
  exact (rvIntegralClass_iso hκ hs h00 hreal he.toGamma).trans (rvIntegralClass_empty hκ hs h00 hreal)

end IntegrationInACVF.Section7.CompletedSection6
