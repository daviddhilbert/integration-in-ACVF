import Integration7.CoordinateRVJacobian

/-! The actual RV determinant of a coordinate permutation, including
its sign. The result concerns defined Jacobians; generic existence is
provided independently. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

def coordinatePermutationLinear {F : Type*} [Field F] {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → F) →ₗ[F] (Fin n → F) := LinearMap.pi (fun i => LinearMap.proj (e i))

theorem coordinatePermutationLinear_det {F : Type*} [Field F] {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (LinearMap.toMatrix' (coordinatePermutationLinear (F := F) e)).det = (Equiv.Perm.sign e : F) := by
  have he : LinearMap.toMatrix' (coordinatePermutationLinear (F := F) e) =
      (1 : Matrix (Fin n) (Fin n) F).submatrix e id := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change (Pi.single j (1 : F) : Fin n → F) (e i) = (1 : Matrix (Fin n) (Fin n) F) (e i) j
    simp only [Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [he, Matrix.det_permute, Matrix.det_one, mul_one]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

def rvPermutationSign (e : Equiv.Perm (Fin n)) : RV := residueRV (Equiv.Perm.sign e : K)

theorem rvPermutationSign_ne_zero (e : Equiv.Perm (Fin n)) : rvPermutationSign (M := M) e ≠ 0 := by
  apply (residueRV_ne_zero _).mpr
  exact ((Equiv.Perm.sign e).isUnit.map (Int.castRingHom K)).ne_zero

theorem rvPermutationSign_absolute (e : Equiv.Perm (Fin n)) :
    RVOperations.absoluteHom (rvPermutationSign (M := M) e) = 1 := by
  have hn : (Equiv.Perm.sign e : K) ≠ 0 :=
    ((Equiv.Perm.sign e).isUnit.map (Int.castRingHom K)).ne_zero
  exact (absolute_residue _).trans (if_neg hn)

theorem normalizedCorrespondence_permuted_coordinate
    (C : Set (Fin (n + n) → RV)) (e : Equiv.Perm (Fin n))
    (hC : ∀ z ∈ C, ∀ i : Fin n, z (productRight n n i) = z (productLeft n n (e i)))
    (t : Fin n → RV) (ht : ∀ i, t i ≠ 0)
    (z : Fin (n + n) → K) (hz : z ∈ normalizedCorrespondence C t (t ∘ e)) (i : Fin n) :
    z (productRight n n i) = z (productLeft n n (e i)) := by
  apply residueRV_injective
  apply mul_left_cancel₀ (ht (e i))
  simpa only [residueScale, productTuple_left, productTuple_right, Function.comp_apply] using hC _ hz.1 i

theorem rvJacobian_eq_permutationSign
    (C : Set (Fin (n + n) → RV)) (e : Equiv.Perm (Fin n))
    (hC : ∀ z ∈ C, ∀ i : Fin n, z (productRight n n i) = z (productLeft n n (e i)))
    (t : Fin n → RV) (ω : RV) (h : IsRVJacobianAt C t (t ∘ e) ω) :
    ω = rvPermutationSign e := by
  obtain ⟨_, ht, _, L, hL, _, hω⟩ := h
  have he : L = coordinatePermutationLinear (F := K) e := by
    apply LinearMap.ext
    intro x
    funext i
    change L x i = x (e i)
    have htan := (hL x (L x)).mpr rfl
    have hh := polynomialTangent_coordinate_eq (normalizedCorrespondence C t (t ∘ e))
      (fun _ => 1) (productTuple x (L x)) htan (productRight n n i) (productLeft n n (e i))
      (fun z hz => normalizedCorrespondence_permuted_coordinate C e hC t ht z hz i)
    simpa only [productTuple_left, productTuple_right] using hh
  subst L
  have hp : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ht i)
  have hprod : (∏ i, (t ∘ e) i) = ∏ i, t i := Equiv.prod_comp e t
  rw [hprod, div_self hp, one_mul, coordinatePermutationLinear_det] at hω
  exact hω

end IntegrationInACVF.Section7
