import IntegrationSection3ACVF.FiniteOrderCellPartition
import IntegrationSection3ACVF.OrderedMonotonePreimages

/-! A target order cell lies in exactly one monotone source piece once
target cuts include images of source endpoints and control the images
of all source cells. No finite-cell invariant is a premise. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.OrderedPairedCellGeometry

open FiniteOrderCells FiniteOrderCellPartition

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem target_cell_inside_image (D : Set α) (E : Set β) (f : α → β)
    (F : Finset α) (G : Finset β) (hF : FiniteOrder.Controls F D)
    (hBij : Set.BijOn f D E) (hPoints : ∀ x ∈ F, x ∈ D → f x ∈ G)
    (hImages : ∀ j : Index F D, FiniteOrder.Controls G (f '' cell F j.val))
    (c : Index G E) : ∃ j : Index F D, cell G c.val ⊆ f '' cell F j.val := by
  obtain ⟨v,hv⟩ := c.property.1
  obtain ⟨x,hxD,hfx⟩ := hBij.2.2 (c.property.2 hv)
  have hxF : x ∉ F := by
    intro hxF
    exact hv.1 (hfx ▸ hPoints x hxF hxD)
  obtain ⟨j,hj⟩ := (point_or_cell hF x hxD).resolve_left hxF
  have hvImage : v ∈ f '' cell F j.val := ⟨x,hj,hfx⟩
  exact ⟨j,controlled (hImages j) c.val v hv hvImage⟩

theorem pullbacks_cover (D : Set α) (E : Set β) (f : α → β) (G : Finset β)
    (hG : FiniteOrder.Controls G E) (hMap : Set.MapsTo f D E) (x : α) :
    x ∈ D ↔ (x ∈ D ∧ f x ∈ G) ∨
      ∃ c : Index G E, x ∈ OrderedMonotonePreimages.pullback D f (cell G c.val) := by
  constructor
  · intro hx
    rcases point_or_cell hG (f x) (hMap hx) with h | ⟨c,hc⟩
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr ⟨c,hx,hc⟩
  · rintro (⟨hx,_⟩ | ⟨c,hx,_⟩)
    · exact hx
    · exact hx

theorem pullbacks_disjoint (D : Set α) (f : α → β) (G : Finset β) {E : Set β}
    (c d : Index G E) (hcd : c ≠ d) :
    Disjoint (OrderedMonotonePreimages.pullback D f (cell G c.val))
      (OrderedMonotonePreimages.pullback D f (cell G d.val)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨_,hc⟩ ⟨_,hd⟩
  have hVal : c.val ≠ d.val := fun he => hcd (Subtype.ext he)
  exact Set.disjoint_left.mp (FiniteOrderCells.disjoint G c.val d.val hVal) hc hd

end IntegrationInACVF.Section3ACVF.OrderedPairedCellGeometry
