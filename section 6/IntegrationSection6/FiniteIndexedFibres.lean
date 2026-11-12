import IntegrationSection6.FiniteCoordinateDeletion

/-! Finite fibres survive assembling families over a finite-fibre base. -/
noncomputable section
open Classical
namespace IntegrationInACVF.Section6

theorem finite_indexed_pair_fibre {X Y V W : Type*}
    (T : Set X) (D : X → Set Y) (f : X → V) (g : X → Y → W)
    (hf : ∀ v, {x | x ∈ T ∧ f x = v}.Finite)
    (hg : ∀ x ∈ T, ∀ w, {y | y ∈ D x ∧ g x y = w}.Finite) (v : V) (w : W) :
    {p : X × Y | p.1 ∈ T ∧ p.2 ∈ D p.1 ∧ f p.1 = v ∧ g p.1 p.2 = w}.Finite := by
  have h := (hf v).biUnion (fun x hx => (hg x hx.1 w).image (fun y => (x,y)))
  apply h.subset
  rintro ⟨x,y⟩ ⟨hx,hy,hfv,hgv⟩
  exact Set.mem_iUnion₂.mpr ⟨x,⟨hx,hfv⟩,⟨y,⟨hy,hgv⟩,rfl⟩⟩

theorem finite_indexed_pair_coordinate_slice {X Y V Z : Type*} {n : ℕ}
    (T : Set X) (D : X → Set Y) (f : X → V) (g : X → Y → (Fin n → Z)) (i : Fin n)
    (hf : ∀ v, {x | x ∈ T ∧ f x = v}.Finite)
    (hg : ∀ x ∈ T, ∀ t : Fin n → Z,
      {r | (∃ y ∈ D x, g x y = r) ∧ ∀ j, j ≠ (i : Fin n) → r j = t j}.Finite)
    (v : V) (t : Fin n → Z) :
    {r | (∃ x ∈ T, f x = v ∧ ∃ y ∈ D x, g x y = r) ∧
      ∀ j, j ≠ i → r j = t j}.Finite := by
  have h := (hf v).biUnion (fun x hx => hg x hx.1 t)
  apply h.subset
  rintro r ⟨⟨x,hx,hfx,y,hy,he⟩,hr⟩
  exact Set.mem_iUnion₂.mpr ⟨x,⟨hx,hfx⟩,⟨⟨y,hy,he⟩,hr⟩⟩

end IntegrationInACVF.Section6
