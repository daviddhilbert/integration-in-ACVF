module

public import Integration7.GammaVolumeDegreeTransport
public import Integration7.VolumeBlowupCoordinatePermutations

@[expose] public section

/-! Simultaneously permuting volume coordinates preserves original-Gamma
common blowups. The common determinant sign is a term constant of the
original base, even in a larger containing context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

set_option maxHeartbeats 2400000 in
theorem GammaVolumeBlowupEquivalent.of_permuted_coordinate_charts
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V U' V' : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V) (e : Equiv.Perm (Fin (k+1)))
    (fU : U.val.underlying ≅ U'.val.underlying) (fV : V.val.underlying ≅ V'.val.underlying)
    (hFU : RVMapGamma (finiteIsoMap fU) B) (hFV : RVMapGamma (finiteIsoMap fV) B)
    (hU : ∀ u, U'.val.underlying.obj.value (finiteIsoMap fU u) = U.val.underlying.obj.value u ∘ e)
    (hV : ∀ v, V'.val.underlying.obj.value (finiteIsoMap fV v) = V.val.underlying.obj.value v ∘ e)
    (hφU : ∀ u, U'.val.form.value (finiteIsoMap fU u) = U.val.form.value u)
    (hφV : ∀ v, V'.val.form.value (finiteIsoMap fV v) = V.val.form.value v) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k U' V' := by
  let c := rvPermutationSign (M := M) e
  have hcC : c.val ∈ C.base := rvPermutationSign_mem C.base e
  have hcB : c.val ∈ Substructure.closure LRV B.real := rvPermutationSign_mem _ e
  have hc0 : c ≠ 0 := rvPermutationSign_ne_zero e
  have hiC := rv_inv_mem_base C.base hcC
  have hiB := rv_inv_mem_base (Substructure.closure LRV B.real) hcB
  have hi0 := inv_ne_zero hc0
  let A := U'.rescale hc c⁻¹ hiC hiB hi0
  let R := V'.rescale hc c⁻¹ hiC hiB hi0
  let eU : RVVolumeIso U.val A.val := RVVolumeIso.of_permuted_coordinates_full hc C fU e hU (by
    intro u
    change c⁻¹ * U'.val.form.value (finiteIsoMap fU u) = c⁻¹ * U.val.form.value u
    rw [hφU])
  let eV : RVVolumeIso V.val R.val := RVVolumeIso.of_permuted_coordinates_full hc C fV e hV (by
    intro v
    change c⁻¹ * V'.val.form.value (finiteIsoMap fV v) = c⁻¹ * V.val.form.value v
    rw [hφV])
  have heU : eU.GammaDefinable B := gamma_volume_iso_of_full_map eU (finiteIsoMap fU)
    (gamma_essential_volume_domain U.val U.property.coordinates) hFU (fun _ => rfl)
  have heV : eV.GammaDefinable B := gamma_volume_iso_of_full_map eV (finiteIsoMap fV)
    (gamma_essential_volume_domain V.val V.property.coordinates) hFV (fun _ => rfl)
  have hAR : GammaVolumeBlowupEquivalent B (C.base : Set M) k A R :=
    ((GammaVolumeBlowupEquivalent.of_iso C B (eU.symm hc C) (heU.symm hc C B)).trans hc C B h).trans hc C B
      (GammaVolumeBlowupEquivalent.of_iso C B eV heV)
  have hscaled := hAR.rescale hc C c hcC hcB hc0
  let eA : RVVolumeIso (A.val.rescale c hcC hc0) U'.val :=
    RVVolumeIso.of_preserving_coordinates_full hc C (Iso.refl U'.val.underlying) (fun _ => rfl) (by
      intro u
      change U'.val.form.value u = c * (c⁻¹ * U'.val.form.value u)
      rw [← mul_assoc,mul_inv_cancel₀ hc0,one_mul])
  let eR : RVVolumeIso (R.val.rescale c hcC hc0) V'.val :=
    RVVolumeIso.of_preserving_coordinates_full hc C (Iso.refl V'.val.underlying) (fun _ => rfl) (by
      intro v
      change V'.val.form.value v = c * (c⁻¹ * V'.val.form.value v)
      rw [← mul_assoc,mul_inv_cancel₀ hc0,one_mul])
  have heA := gamma_volume_iso_of_label_identity hc eA (A.property.rescale hc c hcC hcB hc0) rfl (fun _ => rfl)
  have heR := gamma_volume_iso_of_label_identity hc eR (R.property.rescale hc c hcC hcB hc0) rfl (fun _ => rfl)
  exact ((GammaVolumeBlowupEquivalent.of_iso C B (eA.symm hc C) (heA.symm hc C B)).trans hc C B hscaled).trans hc C B
    (GammaVolumeBlowupEquivalent.of_iso C B eR heR)

end IntegrationInACVF.Section7
