module

public import IntegrationSection3.LocallyFiniteDefinableInjection

@[expose] public section

/-! A relational form of finite-field definable Dedekind finiteness,
suited to first-order transfer without naming a function symbol. -/

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.LocallyFiniteRelations

theorem every_input_has_predecessor {K F₀ ι : Type*} [Field F₀] [Finite F₀]
    [Field K] [Algebra F₀ K] [Algebra.IsAlgebraic F₀ K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (R : Set (ι ⊕ ι → K)) (hR : C.Definable Language.ring R)
    (hRight : ∀ x y z : ι → K, Sum.elim x y ∈ R → Sum.elim x z ∈ R → y = z)
    (hLeft : ∀ x y z : ι → K, Sum.elim x z ∈ R → Sum.elim y z ∈ R → x = y)
    (hNext : ∀ x y : ι → K, Sum.elim x y ∈ R → ∃ z, Sum.elim y z ∈ R) :
    ∀ x y : ι → K, Sum.elim x y ∈ R → ∃ z, Sum.elim z x ∈ R := by
  classical
  let S : Set (ι → K) := {x | ∃ y, Sum.elim x y ∈ R}
  let f : (ι → K) → (ι → K) := fun x => if hx : x ∈ S then Classical.choose hx else 0
  have hChoice (x : ι → K) (hx : x ∈ S) : Sum.elim x (f x) ∈ R := by
    dsimp only [f]
    rw [dif_pos hx]
    exact Classical.choose_spec hx
  have he (z : ι ⊕ ι → K) : z ∈ R ↔ z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl) := by
    have hz : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z := Sum.elim_comp_inl_inr z
    constructor
    · intro h
      have hx : z ∘ Sum.inl ∈ S := ⟨z ∘ Sum.inr,hz.symm ▸ h⟩
      exact ⟨hx,hRight _ _ _ (hz.symm ▸ h) (hChoice _ hx)⟩
    · rintro ⟨hx,hf⟩
      have h := hChoice (z ∘ Sum.inl) hx
      rw [← hf,hz] at h
      exact h
  have hGraph : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)} := by
    convert hR using 1
    exact Set.ext (fun z => (he z).symm)
  have hm : S.MapsTo f S := fun x hx => hNext x (f x) (hChoice x hx)
  have hinj : S.InjOn f := by
    intro x hx y hy hf
    apply hLeft x y (f y)
    · rw [← hf]
      exact hChoice x hx
    · exact hChoice y hy
  have hSurj := LocallyFiniteDefinableInjection.surjOn_of_injOn (F₀ := F₀) C S f hGraph hm hinj
  intro x y hxy
  obtain ⟨z,hz,hfx⟩ := hSurj (show x ∈ S from ⟨y,hxy⟩)
  exact ⟨z,hfx ▸ hChoice z hz⟩

end IntegrationInACVF.Section3.LocallyFiniteRelations
