import Integration7.Section5TwoOrderBaseReductions
import IntegrationSection6.VFParameterCoefficientBases

/-! Section5.8 supplies the actual two-order input after adjoining any
finite VF tuple to a generated base. Definable closure is named only
internally and all graphs descend to the literal original parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem completed_two_order_input_from_generated_closure {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase (closureBase B))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) :
    Section5TwoOrderInput B hκ.le hs hreal := by
  have hD := closureBase_real_small hκ B hreal hgamma
  have h58 : Section5TwoOrderInput (closureBase B) hκ.le hs hD :=
    completed_section5_two_order_input hκ.le hs h00 (closureBase B) hD hGenerated
    δ ((subset_closureBase B).2 hδ) hδ1 (closureBase_field B)
  intro a U hU hfinU σ υ hNe
  exact section5_two_order_input_base_reduction hκ.le hs hreal hD (closureBaseReduction B)
    (subset_closureBase B).2 h58 U hU hfinU σ υ hNe

theorem completed_vf_parameter_two_order_input {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {p : ℕ} (x : Fin p → VF (M := M)) :
    Section5TwoOrderInput ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ.le hs
      (small_union_range hκ.le B.real hreal (fun j => (x j).val)) :=
  completed_two_order_input_from_generated_closure hκ hs h00
    (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))
    (small_union_range hκ.le B.real hreal (fun j => (x j).val)) hgamma
    (vfParameterCoefficientBase_generated hGenerated x) δ hδ hδ1
end IntegrationInACVF.Section7
