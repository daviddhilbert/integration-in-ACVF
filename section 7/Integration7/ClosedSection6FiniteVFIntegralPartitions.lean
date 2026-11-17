module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaVFFiniteRestrictions
public import IntegrationSection6.FiniteVFIntegralPartitions
public import IntegrationSection6.BinaryLiftPartitionValues
public import IntegrationSection6.GammaVFFiniteRestrictions
public import IntegrationSection6.GammaObjectPresentationIsomorphisms

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
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
variable [hgen : Fact (VFGammaGeneratedBase B)]

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))

include hgamma δ hδ hδ1 hc in
theorem vfIntegralValue_partition (A : GammaVFFiniteObject B k)
    (D : Set (Point (M := M) A.val.arity.1 A.val.arity.2)) (hD : GammaSetDefinable B D) (hDA : D ⊆ A.val.domain) :
    vfIntegralValue hκ hs h00 hreal FBase A =
      vfIntegralValue hκ hs h00 hreal FBase (gammaVFRestrict hκ hs h00 hreal A D hD hDA) +
      vfIntegralValue hκ hs h00 hreal FBase (gammaVFComplement hκ hs h00 hreal A D hD) := by
  let R := finiteVFLiftRepresentative hκ hs h00 hreal FBase A
  let U := gammaUniversalObject R.1
  let e : GammaIso B U.toGamma.lift A.val.domain := R.2.symm (gammaLogicInput B)
  obtain ⟨V,W,hClass,⟨v⟩,⟨w⟩⟩ := binary_lift_partition_values hκ hs h00 hreal FBase U e D hD hDA
  have hV := vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
    (gammaVFRestrict hκ hs h00 hreal A D hD hDA) V v
  have hW := vfIntegralValue_of_lift_representation hκ hs h00 hreal FBase hgamma δ hδ hδ1 hc
    (gammaVFComplement hκ hs h00 hreal A D hD) W w
  rw [hV,hW]
  exact (rvIntegralClass_iso hκ hs h00 hreal (gammaObjectPresentationIso R.1 (Set.subset_univ _))).trans hClass

end IntegrationInACVF.Section7.CompletedSection6
