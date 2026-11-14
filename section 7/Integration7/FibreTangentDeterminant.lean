import Integration7.PolynomialTangentFibres
import Integration7.CoordinateRVJacobian
import Integration7.ProductTangentDeterminant

/-! With the head coordinates fixed by a correspondence, the full
tangent determinant is its fixed-head fibre determinant. -/

noncomputable section
open SpecialTransformations.Section7 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

theorem linearMap_det_of_fixed_head {K : Type*} [Field K] {n m : ℕ}
    (L : (Fin (n+m) → K) →ₗ[K] (Fin (n+m) → K))
    (G : (Fin m → K) →ₗ[K] (Fin m → K))
    (hHead : ∀ x, (L x) ∘ Fin.castAdd m = x ∘ Fin.castAdd m)
    (hFibre : ∀ x, (L (Fin.append (fun _ : Fin n => 0) x)) ∘ Fin.natAdd n = G x) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' G).det := by
  classical
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  let A : Matrix (Fin m) (Fin n) K :=
    fun i j => LinearMap.toMatrix' L (Fin.natAdd n i) (Fin.castAdd m j)
  have hRight (j : Fin m) :
      (Pi.single (Fin.natAdd n j) (1 : K) : Fin (n+m) → K) = Fin.append (fun _ => 0) (Pi.single j 1) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Pi.single_apply,Fin.append_left]
      apply if_neg
      intro he
      have h := congrArg Fin.val he
      have hi := i.isLt
      change i.val = n+j.val at h
      omega
    · simp only [Fin.append_right,Pi.single_apply,Fin.natAdd_inj]
  have hblock : (LinearMap.toMatrix' L).submatrix e e =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) K) 0 A (LinearMap.toMatrix' G) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have h := congrFun (hHead (Pi.single (Fin.castAdd m j) 1)) i
        simpa [Matrix.submatrix_apply,e,Matrix.fromBlocks_apply₁₁,LinearMap.toMatrix'_apply,
          Matrix.one_apply,Pi.single_apply] using h
      | inr j =>
        have h := congrFun (hHead (Pi.single (Fin.natAdd n j) 1)) i
        simpa [Matrix.submatrix_apply,e,Matrix.fromBlocks_apply₁₂,LinearMap.toMatrix'_apply,
          hRight] using h
    | inr i =>
      cases j with
      | inl j => rfl
      | inr j =>
        have h := congrFun (hFibre (Pi.single j 1)) i
        simpa only [Matrix.submatrix_apply,e,finSumFinEquiv_apply_right,Matrix.fromBlocks_apply₂₂,
          LinearMap.toMatrix'_apply,← hRight,Function.comp_apply] using h
  rw [← Matrix.det_submatrix_equiv_self e (LinearMap.toMatrix' L),hblock,Matrix.det_fromBlocks_zero₁₂]
  simp

theorem residueJacobian_det_of_fixed_head_fibre {K : Type*} [Field K] {n m : ℕ}
    {C : Set (Fin ((n+m)+(n+m)) → K)} {D : Set (Fin (m+m) → K)}
    (hHead : ∀ z ∈ C, ∀ i : Fin n,
      z (productLeft (n+m) (n+m) (Fin.castAdd m i)) =
        z (productRight (n+m) (n+m) (Fin.castAdd m i)))
    (hFibre : ∀ z ∈ D, insertHeadPair (fun _ : Fin n => 1) (fun _ => 1) z ∈ C)
    (L : (Fin (n+m) → K) →ₗ[K] (Fin (n+m) → K))
    (G : (Fin m → K) →ₗ[K] (Fin m → K))
    (hL : ∀ x y, IsPolynomialTangent C (fun _ => 1) (productTuple x y) ↔ y = L x)
    (hG : ∀ x y, IsPolynomialTangent D (fun _ => 1) (productTuple x y) ↔ y = G x) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' G).det := by
  apply linearMap_det_of_fixed_head L G
  · intro x
    funext i
    have h := polynomialTangent_coordinate_eq C (fun _ => 1) (productTuple x (L x))
      ((hL x (L x)).mpr rfl) (productLeft (n+m) (n+m) (Fin.castAdd m i))
      (productRight (n+m) (n+m) (Fin.castAdd m i)) (fun z hz => hHead z hz i)
    simpa only [Function.comp_apply,productTuple_left,productTuple_right] using h.symm
  · intro x
    have h := polynomialTangent_insertHeadPair (fun _ : Fin n => (1 : K)) (fun _ => 1) hFibre
      ((hG x (G x)).mpr rfl)
    have hp : insertHeadPair (fun _ : Fin n => (1 : K)) (fun _ => 1) (fun _ : Fin (m+m) => 1) =
        fun _ => 1 := by
      apply productTuple_ext <;> intro i <;>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp only [insertHeadPair,productTuple_left,productTuple_right,
            Fin.append_left,Fin.append_right,Function.comp_apply]
    rw [hp] at h
    rw [insertHeadPair_productTuple] at h
    have he := (hL _ _).mp h
    funext i
    simpa only [Function.comp_apply,Fin.append_right] using (congrFun he (Fin.natAdd n i)).symm

end IntegrationInACVF.Section7
