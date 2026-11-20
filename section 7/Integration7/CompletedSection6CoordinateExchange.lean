import Integration7.CompletedVFParameterTwoOrderInputs
import IntegrationSection6.CoordinateExchangeTheorem

/-! Closed Lemma 6.16 over the standing VF/Gamma-generated base.

`IntegrationInACVF.Section6.FiniteRV.lemma_6_16` assumes the Section 5.8
two-order input after adjoining every finite VF tuple. Over a
VF/Gamma-generated base that input is proved by
`completed_vf_parameter_two_order_input`, so the closed statement below
replaces the premise by the standing generation hypothesis. All other
hypotheses are those of the conditional lemma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

namespace CompletedSection6

/-- Lemma 6.16 (exchange of the first two contraction coordinates) over a
VF/Gamma-generated base, with no Section 5.8 premise. -/
theorem lemma_6_16 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction U σ) (E : StandardContraction U υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal (gammaFiniteContraction hκ hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ hs hreal hBS hU hfinU E hE) :=
  FiniteRV.lemma_6_16 hκ hs h00 hreal hgamma δ hδ hδ1 FBase hBS
    (fun x => completed_vf_parameter_two_order_input
      (aleph0_lt_of_small_vf_field_base h00 FBase hreal) hs h00 B hreal hgamma hGenerated
      δ hδ hδ1 x)
    U hU hfinU h0 h1 hTail T E hT hE

end CompletedSection6
end IntegrationInACVF.Section7
