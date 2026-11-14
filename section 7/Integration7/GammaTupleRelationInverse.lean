import Integration7.GammaTupleRelationComposition

/-! Inversion of a relation formula swaps its label blocks and retains
the complete shared parameter tuple. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

def familyRelationInverse (H : Set (Fin ((p+a)+b) → M)) : Set (Fin ((p+b)+a) → M) :=
  (fun w => w ∘ swapLastBlockCoordinates p a b) '' H

theorem familyRelationInverse_definable (sp : Fin p → SortTag)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin b => .rv)) (fun _ : Fin a => .rv))
      (familyRelationInverse H) := by
  have h := hH.image_real (swapLastBlockCoordinates p a b)
  rw [append_swapLastBlocks] at h
  exact h

theorem familyRelationInverse_append (H : Set (Fin ((p+a)+b) → M))
    (z : Fin p → M) (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z y) x ∈ familyRelationInverse H ↔ Fin.append (Fin.append z x) y ∈ H :=
  append_mem_swapLastBlocks_image H z x y

end IntegrationInACVF.Section7
