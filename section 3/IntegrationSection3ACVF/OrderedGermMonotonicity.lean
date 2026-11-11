import IntegrationSection3ACVF.FiniteOrderBounds

/-! Local strict order signs propagate across an interval using a real
finite endpoint controller for the prefixSet set. No ambient Dedekind
completeness, continuity, or Archimedean assumption is used. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.OrderedGermMonotonicity

variable {α β : Type*} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
  [DenselyOrdered α] [LinearOrder β]

def increasing (D : Set α) (f : α → β) (x : α) : Prop :=
  (∃ l, l < x ∧ ∀ y ∈ D, l < y → y < x → f y < f x) ∧
  (∃ u, x < u ∧ ∀ y ∈ D, x < y → y < u → f x < f y)

def prefixSet (f : α → β) (u w : α) : Set α :=
  {z | z ∈ Set.Icc u w ∧ ∀ t, u < t → t ≤ z → f u < f t}

theorem propagate (D : Set α) (f : α → β) (u w : α) (huw : u < w)
    (hD : Set.Icc u w ⊆ D)
    (hLocal : ∀ x ∈ Set.Icc u w, increasing D f x)
    (hControl : ∃ F, FiniteOrder.Controls F (prefixSet f u w)) : f u < f w := by
  have huT : u ∈ prefixSet f u w :=
    ⟨⟨le_rfl,huw.le⟩,fun t hut htu => (not_lt_of_ge htu hut).elim⟩
  have hBound : BddAbove (prefixSet f u w) := ⟨w,fun _ hz => hz.1.2⟩
  obtain ⟨s,hs⟩ := FiniteOrderBounds.exists_isLUB ⟨u,huT⟩ hBound hControl
  have hus : u ≤ s := hs.1 huT
  have hsw : s ≤ w := hs.2 (fun _ hz => hz.1.2)
  have hBelow (t : α) (hts : t < s) : ∃ z ∈ prefixSet f u w, t < z := by
    by_contra hn
    have htU : t ∈ upperBounds (prefixSet f u w) := by
      intro z hz
      by_contra hzt
      exact hn ⟨z,hz,lt_of_not_ge hzt⟩
    exact (not_lt_of_ge (hs.2 htU)) hts
  obtain ⟨⟨l,hls,hLeft⟩,r,hsr,hRight⟩ := hLocal s ⟨hus,hsw⟩
  have hPrefix : ∀ t, u < t → t ≤ s → f u < f t := by
    intro t hut hts
    rcases lt_or_eq_of_le hts with hts | hts
    · obtain ⟨z,hz,htz⟩ := hBelow t hts
      exact hz.2 t hut htz.le
    · rw [hts] at hut ⊢
      obtain ⟨z,hz,hzMax⟩ := hBelow (max l u) (max_lt hls hut)
      have hzs : z ≤ s := hs.1 hz
      rcases lt_or_eq_of_le hzs with hzs | hzs
      · exact (hz.2 z (lt_of_le_of_lt (le_max_right _ _) hzMax) le_rfl).trans
          (hLeft z (hD hz.1) (lt_of_le_of_lt (le_max_left _ _) hzMax) hzs)
      · exact hz.2 s hut hzs.symm.le
  have hEq : s = w := by
    by_contra hne
    have hsw' : s < w := lt_of_le_of_ne hsw hne
    obtain ⟨y,hsy,hy⟩ := exists_between (lt_min hsr hsw')
    have hyr : y < r := hy.trans_le (min_le_left _ _)
    have hyw : y ≤ w := (hy.trans_le (min_le_right _ _)).le
    have hyT : y ∈ prefixSet f u w := by
      refine ⟨⟨hus.trans hsy.le,hyw⟩,?_⟩
      intro t hut hty
      by_cases hts : t ≤ s
      · exact hPrefix t hut hts
      · have hst : s < t := lt_of_not_ge hts
        have hft := hRight t (hD ⟨hut.le,hty.trans hyw⟩) hst (hty.trans_lt hyr)
        rcases lt_or_eq_of_le hus with hus | rfl
        · exact (hPrefix s hus le_rfl).trans hft
        · exact hft
    exact (not_lt_of_ge (hs.1 hyT)) hsy
  rw [hEq] at hPrefix
  exact hPrefix w huw le_rfl

theorem strictMonoOn_of_local (D : Set α) (f : α → β) (hD : Set.OrdConnected D)
    (hLocal : ∀ x ∈ D, increasing D f x)
    (hControl : ∀ u ∈ D, ∀ w ∈ D, u < w →
      ∃ F, FiniteOrder.Controls F (prefixSet f u w)) : StrictMonoOn f D := by
  intro u hu w hw huw
  have hInterval : Set.Icc u w ⊆ D := hD.1 hu hw
  exact propagate D f u w huw hInterval (fun x hx => hLocal x (hInterval hx))
    (hControl u hu w hw huw)

end IntegrationInACVF.Section3ACVF.OrderedGermMonotonicity
