import Integration7.GammaVolumeCriterion

/-! Appending identical nonzero base coordinates preserves the Gamma
Jacobian. This is equality in Gamma, with its actual multiplication. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "RV" => CanonicalRV.RVSort M

theorem rvVolumeGamma_append (t : Fin n → RV) (u : Fin m → RV)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hu : ∀ i, (u i).val ≠ iRVZero)
    (h : ∀ i, (Fin.append t u i).val ≠ iRVZero) :
    rvVolumeGamma (Fin.append t u) h = rvVolumeGamma t ht * rvVolumeGamma u hu := by
  unfold rvVolumeGamma
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.append_left]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [Fin.append_right]

theorem rvGammaJacobian_fixed_head (t : Fin n → RV) (u v : Fin m → RV)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hu : ∀ i, (u i).val ≠ iRVZero)
    (hv : ∀ i, (v i).val ≠ iRVZero)
    (htu : ∀ i, (Fin.append t u i).val ≠ iRVZero) (htv : ∀ i, (Fin.append t v i).val ≠ iRVZero) :
    rvGammaJacobian (Fin.append t u) (Fin.append t v) htu htv = rvGammaJacobian u v hu hv := by
  unfold rvGammaJacobian
  rw [rvVolumeGamma_append t u ht hu htu,rvVolumeGamma_append t v ht hv htv]
  rw [mul_div_mul_comm,div_self',one_mul]

theorem absolute_weight_common_head (t : Fin n → RV) (u v : Fin m → RV) (φ ψ : RV)
    (h : RVOperations.absoluteHom φ * (∏ i, RVOperations.absoluteHom (u i)) =
      RVOperations.absoluteHom ψ * (∏ i, RVOperations.absoluteHom (v i))) :
    RVOperations.absoluteHom φ * (∏ i, RVOperations.absoluteHom (Fin.append t u i)) =
      RVOperations.absoluteHom ψ * (∏ i, RVOperations.absoluteHom (Fin.append t v i)) := by
  rw [Fin.prod_univ_add (a := n) (b := m),Fin.prod_univ_add (a := n) (b := m)]
  simp only [Fin.append_left,Fin.append_right]
  calc
    _ = (∏ i, RVOperations.absoluteHom (t i)) *
      (RVOperations.absoluteHom φ * ∏ i, RVOperations.absoluteHom (u i)) := by ac_rfl
    _ = (∏ i, RVOperations.absoluteHom (t i)) *
      (RVOperations.absoluteHom ψ * ∏ i, RVOperations.absoluteHom (v i)) := congrArg (fun x => _ * x) h
    _ = _ := by ac_rfl

end IntegrationInACVF.Section7
