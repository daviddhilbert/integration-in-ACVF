import Integration7.ProductTangentDeterminant

/-! A defined RV Jacobian of a product correspondence is the product
of its two defined factor Jacobians. Generic existence is kept separate. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "RV" => CanonicalRV.RVSort M

theorem rvJacobian_eq_product_of_projections
    {C : Set (Fin ((n + m) + (n + m)) → RV)}
    {A : Set (Fin (n + n) → RV)} {B : Set (Fin (m + m) → RV)}
    (hA : ∀ z ∈ C, z ∘ coordinatePairIndex (Fin.castAdd m) ∈ A)
    (hB : ∀ z ∈ C, z ∘ coordinatePairIndex (Fin.natAdd n) ∈ B)
    (t s : Fin n → RV) (u v : Fin m → RV) {ω J K : RV}
    (hfull : IsRVJacobianAt C (Fin.append t u) (Fin.append s v) ω)
    (hfirst : IsRVJacobianAt A t s J) (hsecond : IsRVJacobianAt B u v K) : ω = J * K := by
  obtain ⟨_, _, _, L, hL, _, hω⟩ := hfull
  obtain ⟨_, _, _, H, hH, _, hJ⟩ := hfirst
  obtain ⟨_, _, _, G, hG, _, hK⟩ := hsecond
  have hfirst' : ∀ z ∈ normalizedCorrespondence C (Fin.append t u) (Fin.append s v),
      z ∘ coordinatePairIndex (Fin.castAdd m) ∈ normalizedCorrespondence A t s := by
    intro z hz
    simpa only [Function.comp_def, Fin.append_left] using
      normalizedCorrespondence_coordinate_projection (Fin.castAdd m) hA
        (Fin.append t u) (Fin.append s v) z hz
  have hsecond' : ∀ z ∈ normalizedCorrespondence C (Fin.append t u) (Fin.append s v),
      z ∘ coordinatePairIndex (Fin.natAdd n) ∈ normalizedCorrespondence B u v := by
    intro z hz
    simpa only [Function.comp_def, Fin.append_right] using
      normalizedCorrespondence_coordinate_projection (Fin.natAdd n) hB
        (Fin.append t u) (Fin.append s v) z hz
  have hd := residueJacobian_det_of_complementary_projections hfirst' hsecond' L H G hL hH hG
  rw [hω, hd, hJ, hK]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, residueRV_mul]
  rw [← div_mul_div_comm]
  ac_rfl

end IntegrationInACVF.Section7
