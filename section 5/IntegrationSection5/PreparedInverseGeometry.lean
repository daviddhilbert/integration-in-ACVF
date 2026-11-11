import IntegrationSection5.UnaryCellEquivalence

/-! A prepared inverse has open RV-cell images, derived from the actual
two-cell open-to-open geometry and inverse-special affine geometry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {F : DefSet (M := M) S 1 r}

theorem prepared_inverse_open_images (f : Map A B) (hf : Function.Bijective f)
    (hg : CellwiseOpenEquivalence f) (R : SpecialBijection B F)
    (hc : Contractible (Map.comp (Map.inverse f hf) R.inverseMap)) :
    CellwiseOpenMap (Map.comp (Map.inverse f hf) R.inverseMap) := by
  intro E hE hEF hcell
  obtain ⟨z, hz⟩ := hcell
  let D := unaryImage R.inverseMap E
  have hD : IsUnaryOpenPolydisc D := inverse_special_open_images R E hE hEF ⟨z, hz⟩
  have hDcell : ∃ b : B, ∀ p ∈ D, SameRV p b.val := by
    refine ⟨R.inverseMap z, ?_⟩
    rintro p ⟨a, ha, rfl⟩
    exact R.inverse_contractible a z (hz a.val ha)
  have hOut : ∃ a : A, ∀ p ∈ unaryImage (Map.inverse f hf) D, SameRV p a.val := by
    refine ⟨Map.inverse f hf (R.inverseMap z), ?_⟩
    rintro p ⟨b, ⟨a, ha, he⟩, hp⟩
    have hab : R.inverseMap a = b := Subtype.ext he
    subst b
    rw [← hp]
    exact hc a z (hz a.val ha)
  have hi := cellwiseOpenEquivalence_inverse f hf hg
  have hOpen := (hi D (unaryImage_subset R.inverseMap E) hDcell hOut).mp hD
  change IsUnaryOpenPolydisc (unaryImage ((Map.inverse f hf) ∘ R.inverseMap) E)
  rw [unaryImage_comp]
  exact hOpen

end IntegrationInACVF.Section5
