import IntegrationSection6.GammaFamilyMapValidity

/-! First-order validity of an actual function graph on one parameter
row: sorted parameters, a unique output at each domain point, and no
graph points outside the domain. No reverse-fibre bound is required. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {p a b : ℕ}

def functionMapRowValid (sp : Fin p → SortTag)
    (D : Set (Fin (p + a) → M)) (V : Set (Fin ((p + a) + b) → M)) (z : Fin p → M) : Prop :=
  (∀ i, sortEval (sp i) (z i)) ∧
  (∀ x : Fin a → M, Fin.append z x ∈ D → ∃! y : Fin b → M, Fin.append (Fin.append z x) y ∈ V) ∧
  (∀ x : Fin a → M, ∀ y : Fin b → M, Fin.append (Fin.append z x) y ∈ V → Fin.append z x ∈ D)

theorem gamma_functionMapRow_validity_definable
    (sp : Fin p → SortTag) (sx : Fin a → SortTag) (sy : Fin b → SortTag)
    {D : Set (Fin (p + a) → M)} {V : Set (Fin ((p + a) + b) → M)}
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hV : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) V) :
    DefinableOverBase B sp {z | functionMapRowValid sp D V z} := by
  have hUnique := gamma_family_row_unique_definable (Fin.append sp sx) sy hV
  have hTotal := gamma_family_row_subset_definable sp sx hD hUnique
  have hExists := gamma_family_row_exists_definable (Fin.append sp sx) sy hV
  have hSource := gamma_family_row_subset_definable sp sx hExists hD
  have h := hTotal.inter hSource
  convert h using 1
  ext z
  constructor
  · rintro ⟨hs, ht, hd⟩
    exact ⟨⟨hs, ht⟩, hs, fun x ⟨y, hy⟩ => hd x y hy⟩
  · rintro ⟨⟨hs, ht⟩, _, hd⟩
    exact ⟨hs, ht, fun x y hxy => hd x ⟨y, hxy⟩⟩

end IntegrationInACVF.Section7
