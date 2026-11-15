import Integration7.GradedShiftLinearEmbeddings

/-! The literal coefficient at a shifted index recovers each source
component, giving injectivity of the actual shift inclusion. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {F : ℕ → Type} [∀ j, AddCommMonoid (F j)]

theorem graded_shift_to_sum_component (s : ℕ) (f : DirectSum ℕ (fun j => F (j+s))) (j : ℕ) :
    gradedShiftToSum (F := F) s f (j+s) = f j := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero,DFinsupp.zero_apply]
  | add f g hf hg =>
    rw [map_add]
    change (gradedShiftToSum (F := F) s f (j+s)) + (gradedShiftToSum (F := F) s g (j+s)) = f j + g j
    exact congrArg₂ (fun u v => u+v) hf hg
  | of k f =>
    rw [graded_shift_to_sum_of]
    by_cases h : k=j
    · subst k
      rw [DirectSum.of_eq_same,DirectSum.of_eq_same]
    · exact (DirectSum.of_eq_of_ne (β := F) (k+s) (j+s) f (by omega)).trans
        (DirectSum.of_eq_of_ne (β := fun j => F (j+s)) k j f (Ne.symm h)).symm

theorem graded_shift_to_sum_injective (s : ℕ) :
    Function.Injective (gradedShiftToSum (F := F) s) := by
  intro f g h
  apply DFinsupp.ext
  intro j
  exact (graded_shift_to_sum_component s f j).symm.trans
    ((congrArg (fun u : DirectSum ℕ F => u (j+s)) h).trans (graded_shift_to_sum_component s g j))
end IntegrationInACVF.Section7
