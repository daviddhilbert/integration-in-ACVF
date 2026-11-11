import IntegrationSection3ACVF.OrderedCellDecomposition
import IntegrationSection3ACVF.FullGammaBounds

/-! Build actual finite cell-decomposition data from definable open
order cells in an interval with a greatest point. Definable completeness
supplies every right endpoint; endpoint membership is proved. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaCellDecomposition

variable {M ι : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem of_cells (h00 : M ⊨ Axioms.ACVF00) (D : Set (Values.Gamma (M := M)))
    (hD : OrdConnected D) (b : Values.Gamma (M := M)) (hGreatest : IsGreatest D b)
    (P : Finset (Values.Gamma (M := M))) (C : ι → Set (Values.Gamma (M := M)))
    (hCover : ∀ x, x ∈ D ↔ x ∈ P ∨ ∃ i, x ∈ C i)
    (hPoints : ∀ i, Disjoint (P : Set (Values.Gamma (M := M))) (C i))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hNonempty : ∀ i, (C i).Nonempty) (hConnected : ∀ i, OrdConnected (C i))
    (hNoMin : ∀ i, ∀ x ∈ C i, ∃ y ∈ C i, y < x)
    (hNoMax : ∀ i, ∀ x ∈ C i, ∃ y ∈ C i, x < y)
    (hDef : ∀ i, ∃ B : FullBaseAtomicity.Base (M := M), FullGammaSyntax.Scalar B (C i)) :
    ∃ K : OrderedCellDecomposition.Data D ι, K.points = P ∧ K.cells = C := by
  have hSub (i : ι) : C i ⊆ D := fun x hx => (hCover x).mpr (Or.inr ⟨i,hx⟩)
  have hBound (i : ι) : BddAbove (C i) := ⟨b,fun x hx => hGreatest.2 (hSub i hx)⟩
  have hLUB (i : ι) : ∃ r, IsLUB (C i) r := by
    obtain ⟨B,hB⟩ := hDef i
    exact FullGammaBounds.exists_isLUB h00 B hB (hNonempty i) (hBound i)
  choose r hr using hLUB
  have hMem (i : ι) : r i ∈ D := by
    obtain ⟨x,hx⟩ := hNonempty i
    have hxr : x ≤ r i := (hr i).1 hx
    have hrb : r i ≤ b := (hr i).2 (fun x hx => hGreatest.2 (hSub i hx))
    exact hD.out (hSub i hx) hGreatest.1 ⟨hxr,hrb⟩
  let K : OrderedCellDecomposition.Data D ι :=
    { points := P
      cells := C
      cover := hCover
      points_disjoint := hPoints
      cells_disjoint := hDisjoint
      nonempty := hNonempty
      connected := hConnected
      no_min := hNoMin
      no_max := hNoMax
      right := r
      isLUB := hr
      endpoint_mem := hMem }
  exact ⟨K,rfl,rfl⟩

end IntegrationInACVF.Section3ACVF.GammaCellDecomposition
