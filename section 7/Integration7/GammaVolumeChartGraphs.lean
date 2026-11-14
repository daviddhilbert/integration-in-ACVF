import Integration7.GammaDefinableTransforms
import Integration7.TupleVolumeChartGraphs

/-! Uniform certified Jacobian graphs over the original real/Gamma base.
No representative is added to that base in the conclusion. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n : ℕ}

theorem gamma_tupleVolumeChartGraph_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    (sp : Fin p → SortTag) {C : Set (Fin (p+(n+n)) → M)}
    (hC : DefinableOverBase B (Fin.append sp (fun _ : Fin (n+n) => .rv)) C) :
    DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin (n+n) => .rv)) (fun _ : Fin 1 => .rv))
      (tupleVolumeChartGraph σ C) :=
  gamma_definable_transform hc B _ _ (tupleVolumeChartGraph σ)
    (fun q R hR => tupleVolumeChartGraph_uniform hc σ hR)
    (fun C hC => tupleVolumeChartGraph_proper σ sp C hC) hC

theorem gamma_tupleVolumeChartGraphUnion_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : Finset (VolumeChartSupport n))
    (sp : Fin p → SortTag) {C : Set (Fin (p+(n+n)) → M)}
    (hC : DefinableOverBase B (Fin.append sp (fun _ : Fin (n+n) => .rv)) C) :
    DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin (n+n) => .rv)) (fun _ : Fin 1 => .rv))
      {w | ∃ σ ∈ A, w ∈ tupleVolumeChartGraph σ C} := by
  have h := DefinableOverBase.finite_iUnion A (fun σ => tupleVolumeChartGraph σ C)
    (fun σ _ => gamma_tupleVolumeChartGraph_definable hc σ sp hC)
  convert h using 1
  ext w
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq,exists_prop]

end IntegrationInACVF.Section7
