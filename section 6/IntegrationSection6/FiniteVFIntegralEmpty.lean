import IntegrationSection6.FiniteGammaEmptyIsomorphisms
import IntegrationSection6.FiniteVFIntegralValues
import IntegrationSection6.GammaVFFiniteRestrictions
import IntegrationSection6.GammaObjectPresentationIsomorphisms

/-! Integration values of actual VF[k] objects satisfy the definable
binary partition law. The RV pieces and their class identity are constructed
by simultaneous special preparation of a chosen lift presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

include hgamma δ hδ hδ1 h58 in
theorem vfIntegralValue_empty :
    vfIntegralValue hκ hs h00 hreal FBase (gammaVFFinitePresentation B k).empty = 0 := by
  let P := gammaRVFinitePresentation B k
  let U : GammaRVFiniteObject B k := { toGammaRVObject := P.empty.val, finite_volume := P.empty.property }
  have h := vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
    (gammaVFFinitePresentation B k).empty U (gammaIso_reflexive U.lift U.toGammaRVObject.lift_definable)
  rw [h]
  let V := gammaUniversalObject U
  have hV : carrier (rvObjectDomain V.object.obj) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hu
  have he := gammaEmptyIsoAt V hV
  exact (rvIntegralClass_iso hκ hs h00 hreal he.toGamma).trans (rvIntegralClass_empty hκ hs h00 hreal)

end IntegrationInACVF.Section6.FiniteRV
