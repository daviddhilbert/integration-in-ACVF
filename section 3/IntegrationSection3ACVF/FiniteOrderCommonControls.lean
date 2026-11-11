import IntegrationSection3ACVF.FiniteOrderCellPartition
import Mathlib.Data.Finset.Union

/-! A finite family of actual finite endpoint controllers has one
common controller, containing any prescribed finite extra endpoints. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderCommonControls

variable {α ι : Type*} [LinearOrder α] [Finite ι]

theorem exists_common (A : ι → Set α) (hA : ∀ i, ∃ F, FiniteOrder.Controls F (A i))
    (E : Finset α) : ∃ G : Finset α, E ⊆ G ∧ ∀ i, FiniteOrder.Controls G (A i) := by
  classical
  letI := Fintype.ofFinite ι
  choose F hF using hA
  let G := E ∪ Finset.univ.biUnion F
  refine ⟨G,Finset.subset_union_left,?_⟩
  intro i
  apply FiniteOrderCellPartition.controls_mono (F := F i) (hF := hF i)
  intro t ht
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩)

end IntegrationInACVF.Section3ACVF.FiniteOrderCommonControls
