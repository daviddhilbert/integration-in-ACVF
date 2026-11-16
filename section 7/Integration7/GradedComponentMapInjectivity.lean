module

public import Integration7.GradedSemiringActionLinearMaps

@[expose] public section

/-! A map of finite graded sums retains its component formula, so
componentwise injectivity gives injectivity of the assembled additive map. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {F G : ℕ → Type} [∀ j, AddCommMonoid (F j)] [∀ j, AddCommMonoid (G j)]

theorem graded_component_map_to_sum_component (E : ∀ j, F j →+ G j)
    (f : DirectSum ℕ F) (j : ℕ) : gradedComponentMapToSum E f j = E j (f j) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero,DFinsupp.zero_apply]
  | add f g hf hg =>
    rw [map_add]
    change gradedComponentMapToSum E f j + gradedComponentMapToSum E g j = E j (f j+g j)
    exact (congrArg₂ (fun u v => u+v) hf hg).trans ((E j).map_add _ _).symm
  | of k f =>
    rw [graded_component_map_to_sum_of]
    by_cases h : k=j
    · subst k
      rw [DirectSum.of_eq_same,DirectSum.of_eq_same]
    · exact (DirectSum.of_eq_of_ne (β := G) k j (E k f) (Ne.symm h)).trans
        (((E j).map_zero).symm.trans
          (congrArg (E j) (DirectSum.of_eq_of_ne (β := F) k j f (Ne.symm h)).symm))

theorem graded_component_map_to_sum_injective (E : ∀ j, F j →+ G j)
    (hE : ∀ j, Function.Injective (E j)) : Function.Injective (gradedComponentMapToSum E) := by
  intro f g h
  apply DFinsupp.ext
  intro j
  apply hE j
  exact (graded_component_map_to_sum_component E f j).symm.trans
    ((congrArg (fun u : DirectSum ℕ G => u j) h).trans (graded_component_map_to_sum_component E g j))
end IntegrationInACVF.Section7
