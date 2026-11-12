import IntegrationSection6.GammaFamilyMapValidity

/-! Bijective chart validity is first-order: a map schema with reverse
fibre bound one has exactly the specified target image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

def bijectiveMapRowValid (sp : Fin p → SortTag) (sy : Fin b → SortTag)
    (D : Set (Fin (p+a) → M)) (E : Set (Fin (p+b) → M))
    (H : Set (Fin ((p+a)+b) → M)) (z : Fin p → M) : Prop :=
  finiteMapRowValid sp sy D H 1 z ∧
    ∀ y : Fin b → M, Fin.append z y ∈ E ↔ ∃ x : Fin a → M, Fin.append (Fin.append z x) y ∈ H

theorem gamma_bijection_validity_definable (sp : Fin p → SortTag) (sx : Fin a → SortTag)
    (sy : Fin b → SortTag)
    {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {H : Set (Fin ((p+a)+b) → M)}
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hH : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) H) :
    DefinableOverBase B sp {z | bijectiveMapRowValid sp sy D E H z} := by
  have hMap := gamma_finite_map_validity_definable sp sx sy 1 hD hH
  let W := (fun v => v ∘ swapLastBlockCoordinates p a b) '' H
  have hW : DefinableOverBase B (Fin.append (Fin.append sp sy) sx) W := by
    have h := hH.image_real (swapLastBlockCoordinates p a b)
    rw [append_swapLastBlocks] at h
    exact h
  have hImage := gamma_family_row_exists_definable (Fin.append sp sy) sx hW
  have hEq := gamma_family_row_eq_definable sp sy hE hImage
  have h := hMap.inter hEq
  have hRow (z : Fin p → M) (y : Fin b → M) :
      (∃ x : Fin a → M, Fin.append (Fin.append z y) x ∈ W) ↔
      ∃ x : Fin a → M, Fin.append (Fin.append z x) y ∈ H :=
    exists_congr (fun x => append_mem_swapLastBlocks_image H z x y)
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hm,he⟩
    exact ⟨hm,hm.1,fun y => (he y).trans (hRow z y).symm⟩
  · rintro ⟨hm,_,he⟩
    exact ⟨hm,fun y => (he y).trans (hRow z y)⟩

theorem bijectiveMapRowValid.unique_reverse
    {sp : Fin p → SortTag} {sy : Fin b → SortTag}
    {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {H : Set (Fin ((p+a)+b) → M)}
    {z : Fin p → M} (h : bijectiveMapRowValid sp sy D E H z)
    (y : Fin b → M) (hy : Fin.append z y ∈ E) (hsort : ∀ j, sortEval (sy j) (y j)) :
    ∃! x : Fin a → M, Fin.append (Fin.append z x) y ∈ H := by
  obtain ⟨x,hx⟩ := (h.2 y).mp hy
  have hf := h.1.2.2.2 y hsort
  have hle := Set.encard_le_coe_iff_finite_ncard_le.mpr hf
  exact ⟨x,hx,fun x' hx' => Set.encard_le_one_iff.mp hle x' x hx' hx⟩

end IntegrationInACVF.Section6
