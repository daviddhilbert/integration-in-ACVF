import Mathlib.Order.Interval.Set.OrdConnected

/-! Pull an open order cell back through a strictly monotone piece of
an actual injection. No continuity or unproved interval invariant. -/

open Set Classical

namespace IntegrationInACVF.Section3ACVF.OrderedMonotonePreimages

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

def pullback (D : Set α) (f : α → β) (C : Set β) : Set α := D ∩ f ⁻¹' C

theorem subset_piece (D A : Set α) (f : α → β) (C : Set β) (hAD : A ⊆ D)
    (hInj : Set.InjOn f D) (hImage : C ⊆ f '' A) : pullback D f C ⊆ A := by
  rintro x ⟨hx,hfx⟩
  obtain ⟨y,hy,he⟩ := hImage hfx
  have hxy : x = y := hInj hx (hAD hy) he.symm
  exact hxy.symm ▸ hy

theorem nonempty (D A : Set α) (f : α → β) (C : Set β) (hAD : A ⊆ D)
    (hImage : C ⊆ f '' A) (hC : C.Nonempty) : (pullback D f C).Nonempty := by
  obtain ⟨y,hy⟩ := hC
  obtain ⟨x,hx,he⟩ := hImage hy
  exact ⟨x,hAD hx,by change f x ∈ C; rw [he]; exact hy⟩

theorem connected (D A : Set α) (f : α → β) (C : Set β) (hAD : A ⊆ D)
    (hInj : Set.InjOn f D) (hImage : C ⊆ f '' A) (hA : OrdConnected A) (hC : OrdConnected C)
    (hMono : StrictMonoOn f A ∨ StrictAntiOn f A) : OrdConnected (pullback D f C) := by
  have hSub := subset_piece D A f C hAD hInj hImage
  constructor
  intro x hx y hy z hz
  have hxA := hSub hx
  have hyA := hSub hy
  have hzA := hA.out hxA hyA hz
  refine ⟨hAD hzA,?_⟩
  rcases hMono with h | h
  · exact hC.out hx.2 hy.2 ⟨h.monotoneOn hxA hzA hz.1,h.monotoneOn hzA hyA hz.2⟩
  · exact hC.out hy.2 hx.2 ⟨h.antitoneOn hzA hyA hz.2,h.antitoneOn hxA hzA hz.1⟩

theorem no_endpoints (D A : Set α) (f : α → β) (C : Set β) (hAD : A ⊆ D)
    (hInj : Set.InjOn f D) (hImage : C ⊆ f '' A)
    (hMono : StrictMonoOn f A ∨ StrictAntiOn f A)
    (hNoMin : ∀ y ∈ C, ∃ z ∈ C, z < y) (hNoMax : ∀ y ∈ C, ∃ z ∈ C, y < z)
    (x : α) (hx : x ∈ pullback D f C) :
    (∃ y ∈ pullback D f C, y < x) ∧ (∃ y ∈ pullback D f C, x < y) := by
  have hxA := subset_piece D A f C hAD hInj hImage hx
  obtain ⟨l,hl,hlx⟩ := hNoMin (f x) hx.2
  obtain ⟨u,hu,hxu⟩ := hNoMax (f x) hx.2
  obtain ⟨y,hy,hyl⟩ := hImage hl
  obtain ⟨z,hz,hzu⟩ := hImage hu
  have hyP : y ∈ pullback D f C := ⟨hAD hy,by change f y ∈ C; rw [hyl]; exact hl⟩
  have hzP : z ∈ pullback D f C := ⟨hAD hz,by change f z ∈ C; rw [hzu]; exact hu⟩
  have hfy : f y < f x := hyl.symm ▸ hlx
  have hfz : f x < f z := hzu.symm ▸ hxu
  rcases hMono with h | h
  · have hyx : y < x := by
      by_contra hn
      exact (not_lt_of_ge (h.monotoneOn hxA hy (le_of_not_gt hn))) hfy
    have hxz : x < z := by
      by_contra hn
      exact (not_lt_of_ge (h.monotoneOn hz hxA (le_of_not_gt hn))) hfz
    exact ⟨⟨y,hyP,hyx⟩,⟨z,hzP,hxz⟩⟩
  · have hxy : x < y := by
      by_contra hn
      exact (not_lt_of_ge (h.antitoneOn hy hxA (le_of_not_gt hn))) hfy
    have hzx : z < x := by
      by_contra hn
      exact (not_lt_of_ge (h.antitoneOn hxA hz (le_of_not_gt hn))) hfz
    exact ⟨⟨z,hzP,hzx⟩,⟨y,hyP,hxy⟩⟩

end IntegrationInACVF.Section3ACVF.OrderedMonotonePreimages
