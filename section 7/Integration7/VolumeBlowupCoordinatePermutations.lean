import Integration7.VolumeBlowupRescaling
import Integration7.VolumeCoordinatePermutation
import Integration7.PermutationSignParameters

/-! Applying the same permutation of volume coordinates to both
objects preserves common blowups with unchanged density. The two signed
volume isomorphisms are rescaled by their common determinant sign. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VolumeBlowupEquivalent.of_permuted_coordinate_charts
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V U' V' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (e : Equiv.Perm (Fin (k+1)))
    (fU : U.underlying ≅ U'.underlying) (fV : V.underlying ≅ V'.underlying)
    (hU : ∀ u, U'.underlying.obj.value (finiteIsoMap fU u) = U.underlying.obj.value u ∘ e)
    (hV : ∀ v, V'.underlying.obj.value (finiteIsoMap fV v) = V.underlying.obj.value v ∘ e)
    (hφU : ∀ u, U'.form.value (finiteIsoMap fU u) = U.form.value u)
    (hφV : ∀ v, V'.form.value (finiteIsoMap fV v) = V.form.value v) :
    VolumeBlowupEquivalent U' V' := by
  let c := rvPermutationSign (M := M) e
  have hcC : c.val ∈ C.base := rvPermutationSign_mem C.base e
  have hc0 : c ≠ 0 := rvPermutationSign_ne_zero e
  have hiC := rv_inv_mem_base C.base hcC
  have hi0 := inv_ne_zero hc0
  let A := U'.rescale c⁻¹ hiC hi0
  let B := V'.rescale c⁻¹ hiC hi0
  let eU : RVVolumeIso U A := RVVolumeIso.of_permuted_coordinates_full hc C fU e hU (by
    intro u
    change c⁻¹ * U'.form.value (finiteIsoMap fU u) = c⁻¹ * U.form.value u
    rw [hφU])
  let eV : RVVolumeIso V B := RVVolumeIso.of_permuted_coordinates_full hc C fV e hV (by
    intro v
    change c⁻¹ * V'.form.value (finiteIsoMap fV v) = c⁻¹ * V.form.value v
    rw [hφV])
  have hAB : VolumeBlowupEquivalent A B :=
    ((VolumeBlowupEquivalent.of_iso C (eU.symm hc C)).trans hc C h).trans hc C
      (VolumeBlowupEquivalent.of_iso C eV)
  have hscaled := hAB.rescale hc C c hcC hc0
  let eA : RVVolumeIso (A.rescale c hcC hc0) U' :=
    RVVolumeIso.of_preserving_coordinates_full hc C (Iso.refl U'.underlying) (fun _ => rfl) (by
      intro u
      change U'.form.value u = c * (c⁻¹ * U'.form.value u)
      rw [← mul_assoc,mul_inv_cancel₀ hc0,one_mul])
  let eB : RVVolumeIso (B.rescale c hcC hc0) V' :=
    RVVolumeIso.of_preserving_coordinates_full hc C (Iso.refl V'.underlying) (fun _ => rfl) (by
      intro v
      change V'.form.value v = c * (c⁻¹ * V'.form.value v)
      rw [← mul_assoc,mul_inv_cancel₀ hc0,one_mul])
  exact ((VolumeBlowupEquivalent.of_iso C (eA.symm hc C)).trans hc C hscaled).trans hc C
    (VolumeBlowupEquivalent.of_iso C eB)

end IntegrationInACVF.Section7
