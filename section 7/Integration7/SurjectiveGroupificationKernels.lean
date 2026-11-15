import Integration7.SemiringGroupificationGrothendieck
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A surjective semiring map has an exact positive-pair description of
its groupified kernel. The auxiliary additive stabilization is lifted
through the surjection; no additive cancellation in either semiring is
assumed. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {R : Type u} [Semiring R] {T : Type v} [Semiring T]

theorem surjective_groupification_kernel_iff (f : R →+* T) (hf : Function.Surjective f)
    (x : SemiringGroupification R) :
    semiringGroupificationMap f x = 0 ↔
      ∃ a b : R, f a=f b ∧ x=semiringGroupificationOf R a-semiringGroupificationOf R b := by
  constructor
  · intro hx
    obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference x
    rw [map_sub,semiringGroupificationMap_of,semiringGroupificationMap_of] at hx
    obtain ⟨c,hc⟩ := (semiring_groupification_of_eq_iff T (f a) (f b)).mp (sub_eq_zero.mp hx)
    obtain ⟨d,rfl⟩ := hf c
    refine ⟨d+a,d+b,?_,?_⟩
    · rw [map_add,map_add,hc]
    · rw [map_add,map_add]
      abel
  · rintro ⟨a,b,hab,rfl⟩
    rw [map_sub,semiringGroupificationMap_of,semiringGroupificationMap_of,hab,sub_self]

theorem surjective_groupification_kernel_span (f : R →+* T) (hf : Function.Surjective f) :
    RingHom.ker (semiringGroupificationMap f) =
      Ideal.span {x | ∃ a b : R, f a=f b ∧
        x=semiringGroupificationOf R a-semiringGroupificationOf R b} := by
  apply le_antisymm
  · intro x hx
    exact Ideal.subset_span ((surjective_groupification_kernel_iff f hf x).mp (RingHom.mem_ker.mp hx))
  · apply Ideal.span_le.mpr
    intro x hx
    exact RingHom.mem_ker.mpr ((surjective_groupification_kernel_iff f hf x).mpr hx)
end IntegrationInACVF.Section7
