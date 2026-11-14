import Integration7.RVVolumeMorphisms
import Integration7.RVNonzero
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "RV" => CanonicalRV.RVSort M
local notation "Abs" => MonoidWithZeroHom.ValueGroup₀
  (MonoidWithZeroHom.ofClass (Values.presentationValuation (M := M)))

def paperAbsoluteHom : Values.GammaTop (M := M) →*₀ Abs where
  toFun := Values.paperValueEquiv
  map_zero' := Values.paperValue_zero
  map_one' := Values.paperValue_one
  map_mul' := Values.paperValue_mul

@[simp] theorem paperAbsoluteHom_vrv (t : RV) :
    paperAbsoluteHom (Values.vrv t) = RVOperations.absoluteHom t := rfl

theorem rvGammaJacobian_absolute {n : ℕ} (t s : Fin n → RV)
    (ht : ∀ i, (t i).val ≠ iRVZero) (hs : ∀ i, (s i).val ≠ iRVZero) :
    paperAbsoluteHom (rvGammaJacobian t s ht hs).val =
      (∏ i, RVOperations.absoluteHom (s i)) / ∏ i, RVOperations.absoluteHom (t i) := by
  have hdiv (a b : Values.Gamma (M := M)) : (a / b).val = a.val / b.val := by
    rw [div_eq_mul_inv, Values.gamma_val_mul, Values.gamma_val_inv, div_eq_mul_inv]
  have hweight (a : Fin n → RV) (ha : ∀ i, (a i).val ≠ iRVZero) :
      paperAbsoluteHom (rvVolumeGamma a ha).val = ∏ i, RVOperations.absoluteHom (a i) := by
    change paperAbsoluteHom (Values.gammaValHom (rvVolumeGamma a ha)) = _
    rw [rvVolumeGamma, map_prod Values.gammaValHom, map_prod paperAbsoluteHom]
    rfl
  rw [rvGammaJacobian, hdiv, map_div₀, hweight, hweight]

theorem RVVolumeIso.absolute_volumeRatio {S : Set M} {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (u : U.essential.obj.domain) :
    RVOperations.absoluteHom (volumeRatio U V f.iso u) =
      (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap f.iso u) i)) /
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i) := by
  have h := congrArg paperAbsoluteHom (f.gamma u)
  simp only [map_mul, paperAbsoluteHom_vrv, rvGammaJacobian_absolute] at h
  have hv : RVOperations.absoluteHom (V.essentialForm.value (finiteIsoMap f.iso u)) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (V.essentialForm_nonzero _)
  rw [volumeRatio, map_div₀]
  apply div_eq_of_eq_mul hv
  exact h.trans (mul_comm _ _)

end IntegrationInACVF.Section7
