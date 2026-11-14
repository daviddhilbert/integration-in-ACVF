import Integration7.PolynomialTangentImages
import Integration7.PolynomialTangentCoordinatePairs

/-! Tangents of a fixed-head fibre embed as vertical tangents of the
full correspondence. The two heads are constants and have zero velocity. -/

noncomputable section
open MvPolynomial SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

def insertHeadPair {X : Type*} {n m : ℕ} (c d : Fin n → X) (z : Fin (m+m) → X) :
    Fin ((n+m)+(n+m)) → X :=
  productTuple (Fin.append c (z ∘ productLeft m m)) (Fin.append d (z ∘ productRight m m))

@[simp] theorem insertHeadPair_productTuple {X : Type*} {n m : ℕ}
    (c d : Fin n → X) (x y : Fin m → X) :
    insertHeadPair c d (productTuple x y) = productTuple (Fin.append c x) (Fin.append d y) := by
  simp only [insertHeadPair,Function.comp_def,productTuple_left,productTuple_right]

theorem polynomialTangent_insertHeadPair {K : Type*} [Field K] {n m : ℕ}
    (c d : Fin n → K) {C : Set (Fin ((n+m)+(n+m)) → K)} {D : Set (Fin (m+m) → K)}
    (hImage : ∀ z ∈ D, insertHeadPair c d z ∈ C)
    {p v : Fin (m+m) → K} (hv : IsPolynomialTangent D p v) :
    IsPolynomialTangent C (insertHeadPair c d p)
      (insertHeadPair (fun _ => 0) (fun _ => 0) v) := by
  classical
  let f : Fin ((n+m)+(n+m)) → MvPolynomial (Fin (m+m)) K :=
    insertHeadPair (fun i => MvPolynomial.C (c i)) (fun i => MvPolynomial.C (d i)) X
  have hEval (x : Fin (m+m) → K) : (fun i => (f i).eval x) = insertHeadPair c d x := by
    apply productTuple_ext
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [f,insertHeadPair,productTuple_left,Fin.append_left,Fin.append_right,
          Function.comp_apply,eval_C,eval_X]
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [f,insertHeadPair,productTuple_right,Fin.append_left,Fin.append_right,
          Function.comp_apply,eval_C,eval_X]
  have hDeriv : (fun i => ∑ j, (pderiv j (f i)).eval p * v j) =
      insertHeadPair (fun _ => 0) (fun _ => 0) v := by
    apply productTuple_ext
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp [f,insertHeadPair,productTuple_left,Fin.append_left,Fin.append_right,
          pderiv_X,Pi.single_apply,ite_mul]
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp [f,insertHeadPair,productTuple_right,Fin.append_left,Fin.append_right,
          pderiv_X,Pi.single_apply,ite_mul]
  have h := polynomialTangent_polynomialImage f (fun x hx => hEval x ▸ hImage x hx) hv
  rw [hEval,hDeriv] at h
  exact h

end IntegrationInACVF.Section7
