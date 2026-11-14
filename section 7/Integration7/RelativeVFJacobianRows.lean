import Section9.MixedJacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A map that fixes every VF coordinate except one has determinant
equal to the active partial derivative. The assertion is local on the
actual VF chart, including its specified neighbourhood. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section8 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

theorem determinant_of_identity_rows_except {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (i : ι)
    (hA : ∀ j, j ≠ i → A j = (1 : Matrix ι ι R) j) : A.det = A i i := by
  have hrow : (∑ k, A i k • (1 : Matrix ι ι R) k) = A i := by
    funext j
    simp [Matrix.one_apply]
  have heq : A = Matrix.updateRow (1 : Matrix ι ι R) i (A i) := by
    ext j k
    by_cases hj : j = i
    · subst j
      simp
    · simp [Matrix.updateRow_ne hj, hA j hj]
  have hdet := Matrix.det_updateRow_sum (1 : Matrix ι ι R) i (A i)
  rw [hrow, ← heq] at hdet
  simpa using hdet

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "VF" => VFType (M := M)

theorem vf_partial_congr_component_on_ball
    {f g : (Fin n → VF) → Fin m → VF} {a : Fin n → VF}
    {j : Fin n} {i : Fin m} {d : VF} {ρ : Values.Gamma (M := M)}
    (hf : HasVFPartialAt f a j i d)
    (he : ∀ x ∈ vfBall a ρ, f x i = g x i) : HasVFPartialAt g a j i d := by
  intro ε
  obtain ⟨δ,hδ⟩ := hf ε
  refine ⟨max δ ρ,fun t ht hnear => ?_⟩
  have hsmall : ρ.val < Values.vfValueHom t :=
    (show ρ.val ≤ (max δ ρ).val from le_max_right _ _).trans_lt hnear
  have hball : a + Pi.single j t ∈ vfBall a ρ := by
    intro k
    change ρ.val < Values.vfValueHom (a k + (Pi.single j t : Fin n → VF) k - a k)
    rw [add_sub_cancel_left]
    by_cases hk : k = j
    · subst k
      simpa only [Pi.single_eq_same] using hsmall
    · rw [Pi.single_eq_of_ne hk]
      exact gamma_lt_value_zero _
  rw [← he _ hball, ← he _ (mem_vfBall_self a ρ)]
  exact hδ t ht ((show δ.val ≤ (max δ ρ).val from le_max_left _ _).trans_lt hnear)

theorem vf_jacobian_active_partial
    {f : (Fin n → VF) → Fin n → VF} {a : Fin n → VF} {J : VF}
    (hJ : HasVFJacobianAt f a J) (i : Fin n) (ρ : Values.Gamma (M := M))
    (hfixed : ∀ x ∈ vfBall a ρ, ∀ j, j ≠ i → f x j = x j) :
    HasVFPartialAt f a i i J := by
  obtain ⟨A,hA,hdet⟩ := hJ
  have hid : HasVFDerivativeAt (fun x : Fin n → VF => x) a LinearMap.id := by
    simpa only [LinearMap.id_apply, add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : (Fin n → VF) →ₗ[VF] (Fin n → VF)) 0 a
  have hrows : ∀ j, j ≠ i → A j = (1 : Matrix (Fin n) (Fin n) VF) j := by
    intro j hj
    funext k
    have h := vf_partial_congr_component_on_ball (hid.hasPartialAt k j)
      (fun x hx => (hfixed x hx j hj).symm)
    have he := (hA j k).unique h
    simpa only [LinearMap.toMatrix'_id] using he
  have hdiag : A i i = J := (determinant_of_identity_rows_except A i hrows).symm.trans hdet
  exact hdiag ▸ hA i i

end IntegrationInACVF.Section7
