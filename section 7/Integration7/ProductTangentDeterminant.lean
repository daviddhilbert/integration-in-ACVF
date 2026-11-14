import Integration7.PolynomialTangentCoordinatePairs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A full tangent graph that projects to two complementary tangent
graphs has their block-diagonal determinant. -/

noncomputable section
open SpecialTransformations.Section7 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

theorem linearMap_det_of_complementary_blocks {K : Type*} [Field K] {n m : ℕ}
    (L : (Fin (n + m) → K) →ₗ[K] (Fin (n + m) → K))
    (H : (Fin n → K) →ₗ[K] (Fin n → K)) (G : (Fin m → K) →ₗ[K] (Fin m → K))
    (hH : ∀ x, (L x) ∘ Fin.castAdd m = H (x ∘ Fin.castAdd m))
    (hG : ∀ x, (L x) ∘ Fin.natAdd n = G (x ∘ Fin.natAdd n)) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' H).det * (LinearMap.toMatrix' G).det := by
  classical
  have hLL (j : Fin n) : (Pi.single (Fin.castAdd m j) (1 : K) : Fin (n + m) → K) ∘ Fin.castAdd m =
      Pi.single j 1 := by
    funext i
    simp only [Function.comp_apply, Pi.single_apply, Fin.castAdd_inj]
  have hRR (j : Fin m) : (Pi.single (Fin.natAdd n j) (1 : K) : Fin (n + m) → K) ∘ Fin.natAdd n =
      Pi.single j 1 := by
    funext i
    simp only [Function.comp_apply, Pi.single_apply, Fin.natAdd_inj]
  have hRL (j : Fin m) : (Pi.single (Fin.natAdd n j) (1 : K) : Fin (n + m) → K) ∘ Fin.castAdd m = 0 := by
    funext i
    simp only [Function.comp_apply, Pi.single_apply]
    apply if_neg
    intro he
    have hv := congrArg Fin.val he
    change i.val = n + j.val at hv
    have hi := i.isLt
    omega
  have hLR (j : Fin n) : (Pi.single (Fin.castAdd m j) (1 : K) : Fin (n + m) → K) ∘ Fin.natAdd n = 0 := by
    funext i
    simp only [Function.comp_apply, Pi.single_apply]
    apply if_neg
    intro he
    have hv := congrArg Fin.val he
    change n + i.val = j.val at hv
    have hj := j.isLt
    omega
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  have hblock : (LinearMap.toMatrix' L).submatrix e e =
      Matrix.fromBlocks (LinearMap.toMatrix' H) 0 0 (LinearMap.toMatrix' G) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have h := congrFun (hH (Pi.single (Fin.castAdd m j) 1)) i
        simpa only [Matrix.submatrix_apply, e, finSumFinEquiv_apply_left,
          Matrix.fromBlocks_apply₁₁, LinearMap.toMatrix'_apply, hLL, Function.comp_apply] using h
      | inr j =>
        have h := congrFun (hH (Pi.single (Fin.natAdd n j) 1)) i
        simpa only [Matrix.submatrix_apply, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, LinearMap.toMatrix'_apply, hRL, map_zero, Pi.zero_apply,
          Function.comp_apply] using h
    | inr i =>
      cases j with
      | inl j =>
        have h := congrFun (hG (Pi.single (Fin.castAdd m j) 1)) i
        simpa only [Matrix.submatrix_apply, e, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, LinearMap.toMatrix'_apply, hLR, map_zero, Pi.zero_apply,
          Function.comp_apply] using h
      | inr j =>
        have h := congrFun (hG (Pi.single (Fin.natAdd n j) 1)) i
        simpa only [Matrix.submatrix_apply, e, finSumFinEquiv_apply_right,
          Matrix.fromBlocks_apply₂₂, LinearMap.toMatrix'_apply, hRR, Function.comp_apply] using h
  rw [← Matrix.det_submatrix_equiv_self e (LinearMap.toMatrix' L), hblock, Matrix.det_fromBlocks_zero₂₁]

theorem residueJacobian_det_of_complementary_projections {K : Type*} [Field K] {n m : ℕ}
    {C : Set (Fin ((n + m) + (n + m)) → K)}
    {A : Set (Fin (n + n) → K)} {B : Set (Fin (m + m) → K)}
    (hA : ∀ z ∈ C, z ∘ coordinatePairIndex (Fin.castAdd m) ∈ A)
    (hB : ∀ z ∈ C, z ∘ coordinatePairIndex (Fin.natAdd n) ∈ B)
    (L : (Fin (n + m) → K) →ₗ[K] (Fin (n + m) → K))
    (H : (Fin n → K) →ₗ[K] (Fin n → K)) (G : (Fin m → K) →ₗ[K] (Fin m → K))
    (hL : ∀ x y, IsPolynomialTangent C (fun _ => 1) (productTuple x y) ↔ y = L x)
    (hH : ∀ x y, IsPolynomialTangent A (fun _ => 1) (productTuple x y) ↔ y = H x)
    (hG : ∀ x y, IsPolynomialTangent B (fun _ => 1) (productTuple x y) ↔ y = G x) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' H).det * (LinearMap.toMatrix' G).det := by
  apply linearMap_det_of_complementary_blocks L H G
  · intro x
    have ht := polynomialTangent_projection (coordinatePairIndex (Fin.castAdd m))
      (coordinatePairIndex_injective _ (Fin.castAdd_injective n m)) hA ((hL x (L x)).mpr rfl)
    rw [productTuple_comp_coordinatePairIndex] at ht
    exact (hH _ _).mp ht
  · intro x
    have ht := polynomialTangent_projection (coordinatePairIndex (Fin.natAdd n))
      (coordinatePairIndex_injective _ (Fin.natAdd_injective m n)) hB ((hL x (L x)).mpr rfl)
    rw [productTuple_comp_coordinatePairIndex] at ht
    exact (hG _ _).mp ht

end IntegrationInACVF.Section7
