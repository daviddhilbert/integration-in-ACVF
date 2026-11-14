import Integration7.RVVolumeMorphisms

/-! A defined RV Jacobian of a diagonal volume correspondence is one.
The generic existence theorem is used separately, so no smoothness of an
arbitrary definable image is assumed here. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

set_option backward.isDefEq.respectTransparency true in
theorem polynomialTangent_coordinate_eq {K : Type*} [Field K] {d : ℕ}
    (C : Set (Fin d → K)) (p v : Fin d → K) (hv : IsPolynomialTangent C p v)
    (i j : Fin d) (hC : ∀ z ∈ C, z i = z j) : v i = v j := by
  have hp : ∀ z ∈ C, (X i - X j : MvPolynomial (Fin d) K).eval z = 0 := by
    intro z hz
    calc
      (eval (R := K) z) (X i - X j) = (eval (R := K) z) (X i) - (eval (R := K) z) (X j) :=
        map_sub (eval (R := K) z) _ _
      _ = z i - z j := by rw [eval_X, eval_X]
      _ = 0 := sub_eq_zero.mpr (hC z hz)
  have h := hv (X i - X j) hp
  have hd (l r : Fin d) :
      (pderiv l (X r : MvPolynomial (Fin d) K)).eval p = if r = l then 1 else 0 := by
    rw [pderiv_X]
    by_cases hr : r = l
    · simp only [Pi.single_apply, hr, ite_true, map_one]
    · simp only [Pi.single_apply, hr, ite_false, map_zero]
  have hterm (l : Fin d) :
      (pderiv l (X i - X j : MvPolynomial (Fin d) K)).eval p * v l =
        (if i = l then v l else 0) - (if j = l then v l else 0) := by
    rw [map_sub, map_sub, hd, hd, sub_mul]
    simp only [ite_mul, one_mul, zero_mul]
  have he : v i - v j = 0 := by
    simp only [hterm, Finset.sum_sub_distrib] at h
    simpa only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h
  exact sub_eq_zero.mp he

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

theorem normalizedCorrespondence_coordinate_eq
    (C : Set (Fin (n + n) → RV))
    (hC : ∀ z ∈ C, ∀ i : Fin n, z (productLeft n n i) = z (productRight n n i))
    (t : Fin n → RV) (ht : ∀ i, t i ≠ 0)
    (z : Fin (n + n) → K) (hz : z ∈ normalizedCorrespondence C t t) (i : Fin n) :
    z (productLeft n n i) = z (productRight n n i) := by
  apply residueRV_injective
  apply mul_left_cancel₀ (ht i)
  have h := hC _ hz.1 i
  simpa only [residueScale, productTuple_left, productTuple_right] using h

theorem rvJacobian_eq_one_of_diagonal
    (C : Set (Fin (n + n) → RV))
    (hC : ∀ z ∈ C, ∀ i : Fin n, z (productLeft n n i) = z (productRight n n i))
    (t : Fin n → RV) (ω : RV) (h : IsRVJacobianAt C t t ω) : ω = 1 := by
  obtain ⟨_, ht, _, L, hL, _, hω⟩ := h
  have he : L = LinearMap.id := by
    apply LinearMap.ext
    intro x
    funext i
    have htan := (hL x (L x)).mpr rfl
    have hh := polynomialTangent_coordinate_eq (normalizedCorrespondence C t t)
      (fun _ => 1) (productTuple x (L x)) htan (productLeft n n i) (productRight n n i)
      (fun z hz => normalizedCorrespondence_coordinate_eq C hC t ht z hz i)
    simpa only [productTuple_left, productTuple_right, LinearMap.id_apply] using hh.symm
  subst L
  have hp : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ht i)
  simpa [hp] using hω

end IntegrationInACVF.Section7
