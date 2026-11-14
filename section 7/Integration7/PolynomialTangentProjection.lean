import Integration7.RVJacobianRestriction
import Mathlib.Algebra.MvPolynomial.Variables

/-! Tangent vectors project along coordinate injections. -/
noncomputable section
open MvPolynomial
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

theorem polynomialTangent_projection {K : Type*} [Field K] {d e : ℕ}
    (ρ : Fin e → Fin d) (hρ : Function.Injective ρ)
    {C : Set (Fin d → K)} {D : Set (Fin e → K)}
    (hCD : ∀ z ∈ C, z ∘ ρ ∈ D) {p v : Fin d → K}
    (hv : IsPolynomialTangent C p v) : IsPolynomialTangent D (p ∘ ρ) (v ∘ ρ) := by
  classical
  intro P hP
  have hvanish : ∀ z ∈ C, (rename ρ P).eval z = 0 := by
    intro z hz
    rw [eval_rename]
    exact hP _ (hCD z hz)
  have hzero := hv (rename ρ P) hvanish
  have hout (j : Fin d) (hj : j ∉ Set.range ρ) :
      (pderiv j (rename ρ P)).eval p * v j = 0 := by
    have hd : pderiv j (rename ρ P) = 0 := pderiv_eq_zero_of_notMem_vars (by
      intro h
      obtain ⟨i, _, hi⟩ := mem_vars_rename ρ P h
      exact hj ⟨i, hi⟩)
    rw [hd, map_zero, zero_mul]
  have hsum := Fintype.sum_of_injective ρ hρ
    (fun i => (pderiv i P).eval (p ∘ ρ) * (v ∘ ρ) i)
    (fun j => (pderiv j (rename ρ P)).eval p * v j) hout
    (fun i => by rw [pderiv_rename hρ, eval_rename]; rfl)
  exact hsum.trans hzero

end IntegrationInACVF.Section7
