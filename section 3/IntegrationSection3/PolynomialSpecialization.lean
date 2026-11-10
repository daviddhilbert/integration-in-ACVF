module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Algebra

@[expose] public section

/-! A nonzero bivariate polynomial has only finitely many parameters
where the corresponding univariate polynomial vanishes identically. -/

open Set

namespace IntegrationInACVF.Section3.PolynomialSpecialization

variable {K : Type*} [Field K]

noncomputable def specialize (F : Polynomial (Polynomial K)) (y : K) : Polynomial K :=
  F.map (Polynomial.evalRingHom y)

theorem finite_zero_specializations (F : Polynomial (Polynomial K)) (hF : F ≠ 0) :
    {y | specialize F y = 0}.Finite := by
  classical
  have hex : ∃ i : ℕ, F.coeff i ≠ 0 := by
    by_contra hn
    apply hF
    apply Polynomial.ext
    intro i
    change F.coeff i = 0
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  apply (Polynomial.finite_setOfPred_isRoot hi).subset
  intro y hy
  change (F.coeff i).eval y = 0
  have hc := congrArg (fun p : Polynomial K => p.coeff i) hy
  simpa only [specialize,Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coe_evalRingHom] using hc

end IntegrationInACVF.Section3.PolynomialSpecialization
