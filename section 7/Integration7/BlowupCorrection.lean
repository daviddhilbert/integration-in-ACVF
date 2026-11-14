import Integration7.RVVolumeMorphisms

/-! The scalar correction for a head Jacobian. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "RV" => CanonicalRV.RVSort M

theorem rvJacobian_ne_zero {n : ℕ} {D : Set (Fin (n + n) → RV)} {t s : Fin n → RV} {ω : RV}
    (h : IsRVJacobianAt D t s ω) : ω ≠ 0 := by
  obtain ⟨_, ht, hs, L, _, hdet, rfl⟩ := h
  exact mul_ne_zero
    (div_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hs i))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => ht i))) ((residueRV_ne_zero _).mpr hdet)

def blowupCorrection (J a b r s : RV) : RV := (a / b) / (J * (s / r))

theorem blowupCorrection_cancel (J a b r s : RV) (hJ : J ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    blowupCorrection J a b r s * (J * (s / r)) = a / b :=
  div_mul_cancel₀ _ (mul_ne_zero hJ (div_ne_zero hs hr))

theorem blowupCorrection_absolute (J a b r s : RV) (hJ : J ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : RVOperations.absoluteHom (a / b) =
      RVOperations.absoluteHom J * (RVOperations.absoluteHom s / RVOperations.absoluteHom r)) :
    RVOperations.absoluteHom (blowupCorrection J a b r s) = 1 := by
  have hn : RVOperations.absoluteHom (J * (s / r)) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (mul_ne_zero hJ (div_ne_zero hs hr))
  unfold blowupCorrection
  rw [map_div₀, h, ← map_div₀, ← map_mul]
  exact div_self hn

end IntegrationInACVF.Section7
