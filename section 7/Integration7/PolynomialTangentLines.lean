import Integration7.PolynomialTangentProjection
import Section9.RVJacobianDerivations
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Roots

/-! A punctured affine coordinate line supplies its velocity tangent.
The proof uses polynomial identities over an infinite field. -/

noncomputable section
open MvPolynomial SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

theorem polynomialTangent_of_punctured_coordinate_line
    {K : Type*} [Field K] [Infinite K] {d : ℕ}
    (I : Finset (Fin d)) (C : Set (Fin d → K))
    (hC : ∀ a : K, a ≠ 0 → (fun i => if i ∈ I then a else 1) ∈ C) :
    IsPolynomialTangent C (fun _ => 1) (fun i => if i ∈ I then 1 else 0) := by
  classical
  intro P hP
  let z (i : Fin d) : Polynomial K := if i ∈ I then Polynomial.X else 1
  have heval (Q : MvPolynomial (Fin d) K) (a : K) :
      (MvPolynomial.aeval z Q).eval a = Q.eval (fun i => if i ∈ I then a else 1) := by
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR => simp only [map_add, Polynomial.eval_add, hQ, hR]
    | mul_X Q i hQ =>
      simp only [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hQ, MvPolynomial.eval_X]
      congr 1
      by_cases hi : i ∈ I <;> simp [z, hi]
  have hq : MvPolynomial.aeval z P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : Set.Infinite {a : K | a ≠ 0} := by
      exact (Set.infinite_univ.sdiff (Set.finite_singleton (0 : K))).mono (fun _ ha => ha.2)
    apply hinf.mono
    intro a ha
    change (MvPolynomial.aeval z P).eval a = 0
    rw [heval]
    exact hP _ (hC a ha)
  have hderiv := derivation_aeval_eq_sum (Polynomial.derivative' (R := K)) z P
  have hd (i : Fin d) : (Polynomial.derivative' (R := K) (z i)).eval 1 =
      if i ∈ I then 1 else 0 := by
    by_cases hi : i ∈ I <;> simp [z, hi, Polynomial.derivative'_apply]
  have h := congrArg (Polynomial.eval (1 : K)) hderiv
  simp only [hq, map_zero, Polynomial.eval_zero, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, heval, ite_self, hd] at h
  exact h.symm

end IntegrationInACVF.Section7
