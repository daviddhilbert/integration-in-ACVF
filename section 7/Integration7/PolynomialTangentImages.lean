import Integration7.PolynomialTangentProjection
import Section9.RVJacobianDerivations

/-! Polynomial maps carry the tangent vectors defined by vanishing
polynomials to their differential images. -/

noncomputable section
open MvPolynomial SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

theorem polynomialTangent_polynomialImage {K : Type*} [Field K] {d e : ℕ}
    (f : Fin d → MvPolynomial (Fin e) K)
    {C : Set (Fin d → K)} {D : Set (Fin e → K)}
    (hImage : ∀ x ∈ D, (fun i => (f i).eval x) ∈ C)
    {p v : Fin e → K} (hv : IsPolynomialTangent D p v) :
    IsPolynomialTangent C (fun i => (f i).eval p)
      (fun i => ∑ j, (pderiv j (f i)).eval p * v j) := by
  classical
  have hEval (Q : MvPolynomial (Fin d) K) (x : Fin e → K) :
      (aeval f Q).eval x = Q.eval (fun i => (f i).eval x) := by
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR => simp only [map_add,hQ,hR]
    | mul_X Q i hQ => simp only [map_mul,aeval_X,eval_X,hQ]
  intro Q hQ
  have hZero := hv (aeval f Q) (fun x hx => by rw [hEval]; exact hQ _ (hImage x hx))
  have hDeriv (j : Fin e) :
      (pderiv j (aeval f Q)).eval p =
        ∑ i, (pderiv i Q).eval (fun l => (f l).eval p) * (pderiv j (f i)).eval p := by
    have h := congrArg (eval p) (derivation_aeval_eq_sum (pderiv j) f Q)
    simpa only [map_sum,map_mul,hEval] using h
  calc
    _ = ∑ j, (∑ i, (pderiv i Q).eval (fun l => (f l).eval p) *
        (pderiv j (f i)).eval p) * v j := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
      exact Finset.sum_comm
    _ = ∑ j, (pderiv j (aeval f Q)).eval p * v j := by simp only [hDeriv]
    _ = 0 := hZero

end IntegrationInACVF.Section7
