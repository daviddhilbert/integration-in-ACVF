import IntegrationSection3ACVF.FiniteOrderBounds
import Section3.GammaCounting
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Set.Card

/-! Strict local extrema on a possibly non-Archimedean ordered group.
The proof uses genuine uniform finite row bounds supplied separately;
no countability or Archimedean argument is used. -/

open Set Classical
open SpecialTransformations.Section3
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.OrderedLocalExtrema

variable {G β : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G] [LinearOrder β]

def radiusRow (D : Set G) (f : G → β) (δ : G) : Set G :=
  {x | 1 < δ ∧ x ∈ D ∧ ∀ y ∈ D, y < x*δ → x < y*δ → y ≠ x → f x < f y}

def localMin (D : Set G) (f : G → β) : Set G :=
  {x | x ∈ D ∧ ∃ l u, l < x ∧ x < u ∧
    ∀ y ∈ D, l < y → y < u → y ≠ x → f x < f y}

theorem radiusRow_no_interval (D : Set G) (f : G → β) (δ l u : G)
    (hlu : l < u) (hSub : Set.Ioo l u ⊆ radiusRow D f δ) : False := by
  obtain ⟨x,hlx,hxu⟩ := exists_between hlu
  have hx := hSub ⟨hlx,hxu⟩
  have hxδ : x < x*δ := by simpa only [mul_one] using mul_lt_mul_right hx.1 x
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hxu hxδ)
  have hyu : y < u := hy.trans_le (min_le_left _ _)
  have hyxδ : y < x*δ := hy.trans_le (min_le_right _ _)
  have hyRow := hSub ⟨hlx.trans hxy,hyu⟩
  have hyδ : y < y*δ := by simpa only [mul_one] using mul_lt_mul_right hx.1 y
  have hxyδ : x < y*δ := hxy.trans hyδ
  exact (not_lt_of_gt (hx.2.2 y hyRow.2.1 hyxδ hxyδ hxy.ne'))
    (hyRow.2.2 x hx.2.1 hxyδ hyxδ hxy.ne)

theorem radiusRow_finite (D : Set G) (f : G → β) (δ : G)
    (hControl : ∃ F, FiniteOrder.Controls F (radiusRow D f δ)) :
    (radiusRow D f δ).Finite := by
  rcases FiniteOrderBounds.finite_or_contains_interval hControl with h | ⟨l,u,hlu,hSub⟩
  · exact h
  · exact (radiusRow_no_interval D f δ l u hlu hSub).elim

theorem radiusRow_shrink (D : Set G) (f : G → β) {δ ε : G}
    (hδ : 1 < δ) (hδε : δ ≤ ε) : radiusRow D f ε ⊆ radiusRow D f δ := by
  rintro x ⟨_,hx,hMin⟩
  refine ⟨hδ,hx,?_⟩
  intro y hy hyδ hxδ hne
  exact hMin y hy (hyδ.trans_le (mul_le_mul_right hδε x))
    (hxδ.trans_le (mul_le_mul_right hδε y)) hne

theorem localMin_has_radius (D : Set G) (f : G → β) {x : G}
    (hx : x ∈ localMin D f) : ∃ δ, x ∈ radiusRow D f δ := by
  obtain ⟨hxD,l,u,hlx,hxu,hMin⟩ := hx
  have hLim : (1 : G) < min (x/l) (u/x) :=
    lt_min (one_lt_div'.mpr hlx) (one_lt_div'.mpr hxu)
  obtain ⟨δ,hδ,hδLim⟩ := exists_between hLim
  have hlδx : l*δ < x := by
    have h := (lt_div_iff_mul_lt).mp (hδLim.trans_le (min_le_left _ _))
    simpa only [mul_comm] using h
  have hxδu : x*δ < u := by
    have h := (lt_div_iff_mul_lt).mp (hδLim.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h
  refine ⟨δ,hδ,hxD,?_⟩
  intro y hy hyδ hxδ hne
  have hly : l < y := by
    by_contra hn
    have hyδx : y*δ < x := (mul_le_mul_left (le_of_not_gt hn) δ).trans_lt hlδx
    exact (not_lt_of_gt hyδx) hxδ
  exact hMin y hy hly (hyδ.trans hxδu) hne

theorem localMin_iff_radius (D : Set G) (f : G → β) (x : G) :
    x ∈ localMin D f ↔ ∃ δ, x ∈ radiusRow D f δ := by
  constructor
  · exact localMin_has_radius D f
  · rintro ⟨δ,hδ,hx,hMin⟩
    have hlx : x/δ < x := (div_lt_self_iff x).mpr hδ
    have hxu : x < x*δ := by simpa only [mul_one] using mul_lt_mul_right hδ x
    refine ⟨hx,x/δ,x*δ,hlx,hxu,?_⟩
    intro y hy hly hyu hne
    exact hMin y hy hyu (div_lt_iff_lt_mul.mp hly) hne

theorem localMin_no_interval_of_uniform_bound (D : Set G) (f : G → β) (N : ℕ)
    (hBound : ∀ δ, (radiusRow D f δ).Finite ∧ (radiusRow D f δ).ncard ≤ N)
    (l u : G) (hlu : l < u) (hSub : Set.Ioo l u ⊆ localMin D f) : False := by
  classical
  have hMany : ∃ x : Fin (N+1) → G, Function.Injective x ∧ ∀ i, x i ∈ Set.Ioo l u := by
    by_contra hn
    exact (Set.Ioo_infinite hlu) ((GammaParameters.no_injection_iff_finite_ncard_le).mp hn).1
  obtain ⟨x,hInj,hMem⟩ := hMany
  choose r hr using fun i => localMin_has_radius D f (hSub (hMem i))
  let R := Finset.univ.image r
  have hR : R.Nonempty := ⟨r 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  let δ := R.min' hR
  have hδ : (1 : G) < δ := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (R.min'_mem hR)
    change (1 : G) < R.min' hR
    rw [← hi]
    exact (hr i).1
  have hAll (i : Fin (N+1)) : x i ∈ radiusRow D f δ :=
    radiusRow_shrink D f hδ (R.min'_le _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) (hr i)
  exact (GammaParameters.no_injection_iff_finite_ncard_le).mpr (hBound δ) ⟨x,hInj,hAll⟩

theorem localMin_finite (D : Set G) (f : G → β) (N : ℕ)
    (hBound : ∀ δ, (radiusRow D f δ).Finite ∧ (radiusRow D f δ).ncard ≤ N)
    (hControl : ∃ F, FiniteOrder.Controls F (localMin D f)) :
    (localMin D f).Finite := by
  rcases FiniteOrderBounds.finite_or_contains_interval hControl with h | ⟨l,u,hlu,hSub⟩
  · exact h
  · exact (localMin_no_interval_of_uniform_bound D f N hBound l u hlu hSub).elim

end IntegrationInACVF.Section3ACVF.OrderedLocalExtrema
