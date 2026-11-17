module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6FiniteVFIntegralValues
public import IntegrationSection6.GammaVFFiniteRestrictions
public import IntegrationSection6.FiniteVFIntegralValues

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
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)

def gammaVFRestrict (A : GammaVFFiniteObject B k)
    (D : Set (Point (M := M) A.val.arity.1 A.val.arity.2)) (hD : GammaSetDefinable B D) (hDA : D ⊆ A.val.domain) :
    GammaVFFiniteObject B k :=
  ⟨⟨A.val.arity,D,hD,(gamma_dim_le_iff_rank hκ hs h00 hreal hD).mpr
      (fun p hp => gamma_rank_of_dimension A.val.dimension p (hDA hp))⟩,
    fun x => (A.property x).subset (fun r hr => hDA hr)⟩

def gammaVFComplement (A : GammaVFFiniteObject B k)
    (D : Set (Point (M := M) A.val.arity.1 A.val.arity.2)) (hD : GammaSetDefinable B D) : GammaVFFiniteObject B k :=
  gammaVFRestrict hκ hs h00 hreal A (A.val.domain \ D) ((gammaLogicInput B).sdiff A.val.definable hD) (fun _ h => h.1)

end IntegrationInACVF.Section7.CompletedSection6
