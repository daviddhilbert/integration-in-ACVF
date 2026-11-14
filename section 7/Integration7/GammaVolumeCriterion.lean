import Integration7.GammaAbsoluteValues

/-! Equivalent absolute-value and Gamma forms of the pointwise volume
equation. No generic RV-Jacobian condition is inferred from this equation. -/

noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem gammaVolumeEquation_of_absoluteRatio
    {U V : PositiveRVVolumeObject (M := M) S k} (e : U.essential ≅ V.essential)
    (u : U.essential.obj.domain)
    (h : RVOperations.absoluteHom (volumeRatio U V e u) =
      (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap e u) i)) /
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) :
    Values.vrv (U.essentialForm.value u) =
      Values.vrv (V.essentialForm.value (finiteIsoMap e u)) *
        (rvGammaJacobian (U.essential.obj.value u)
          (V.essential.obj.value (finiteIsoMap e u))
          (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e u))).val := by
  apply (Values.paperValueEquiv (M := M)).injective
  change paperAbsoluteHom _ = paperAbsoluteHom _
  rw [map_mul, paperAbsoluteHom_vrv, paperAbsoluteHom_vrv, rvGammaJacobian_absolute]
  have hv : RVOperations.absoluteHom (V.essentialForm.value (finiteIsoMap e u)) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (V.essentialForm_nonzero _)
  rw [volumeRatio, map_div₀] at h
  exact ((div_eq_iff hv).mp h).trans (mul_comm _ _)

end IntegrationInACVF.Section7
