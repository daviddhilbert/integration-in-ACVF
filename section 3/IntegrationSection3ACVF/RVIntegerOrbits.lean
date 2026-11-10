import IntegrationSection3ACVF.GammaCosetGeometry
import Section3.AdditiveRadial

/-! Nonzero natural scalars give an infinite orbit inside one actual
RV value fibre in residue characteristic zero. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.RVIntegerOrbits

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nat_value (h00 : M ⊨ Axioms.ACVF00) (n : ℕ) (hn : n ≠ 0) :
    Values.vfValueHom (n : VFType (M := M)) = 1 := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hu := GammaCosetGeometry.valuation_nat_unit h00 v hv n hn
  have h1 : VFValued.predV (1 : VFType (M := M)) (n : VFType (M := M)) :=
    (hv _ _).mpr (by simp only [map_one,hu,le_refl])
  have h2 : VFValued.predV (n : VFType (M := M)) (1 : VFType (M := M)) :=
    (hv _ _).mpr (by simp only [map_one,hu,le_refl])
  have he := le_antisymm ((Values.vf_pred_iff_gamma_le _ _).mp h1)
    ((Values.vf_pred_iff_gamma_le _ _).mp h2)
  exact he.trans (map_one Values.vfValueHom)

theorem orbit_injective (h00 : M ⊨ Axioms.ACVF00) (r : VFType (M := M)) (hr : r ≠ 0) :
    Function.Injective (fun n : ℕ => CanonicalRV.encodedRv (((n+1 : ℕ) : VFType (M := M))*r)) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have h := AdditiveBalls.affine_rv_injective v hv h00 r 0 hr (by rw [map_zero]; exact zero_le)
  simpa only [zero_add,AdditiveBalls.multiples] using h

theorem orbit_value (h00 : M ⊨ Axioms.ACVF00) (r : VFType (M := M)) (n : ℕ) :
    Values.vfValueHom (((n+1 : ℕ) : VFType (M := M))*r) = Values.vfValueHom r := by
  rw [map_mul,nat_value h00 (n+1) (Nat.succ_ne_zero n),one_mul]

end IntegrationInACVF.Section3ACVF.RVIntegerOrbits
