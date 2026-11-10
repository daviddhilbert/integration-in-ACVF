import IntegrationSection3ACVF.GammaCosetGeometry
import IntegrationSection3.ValuationProgressions
import Section3.DiscCentres

/-! A sequence of equal nonzero RV increments has the RV of its integer
multiple displacement. Residue characteristic zero is explicit. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVIntegerSequences

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem sequence_rv (h00 : M ⊨ Axioms.ACVF00)
    (a : ℕ → VFType (M := M)) (b : VFType (M := M)) (hb : b ≠ 0)
    (hstep : ∀ j, iRv (a (j+1)-a j).val = iRv b.val) (n : ℕ) (hn : n ≠ 0) :
    iRv (a n-a 0).val = iRv ((n : VFType (M := M))*b).val := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hstepv (j : ℕ) : v (a (j+1)-a j-b) < v b := by
    have h := (CanonicalRV.encoded_eq_iff_close (a (j+1)-a j).property b.property
      (fun he => hb (Subtype.ext he))).mp (hstep j)
    exact lt_of_not_ge (fun he => h ((hv _ _).mpr he))
  have he := ValuationProgressions.error_lt v a b hb hstepv n
  have hnb : v ((n : VFType (M := M))*b) = v b := by
    rw [map_mul,GammaCosetGeometry.valuation_nat_unit h00 v hv n hn,one_mul]
  have hnb0 : (n : VFType (M := M))*b ≠ 0 :=
    (v.ne_zero_iff).mp (by rw [hnb]; exact (v.ne_zero_iff).mpr hb)
  apply Balls.rv_eq_of_sub_lt v hv (a n-a 0) ((n : VFType (M := M))*b) hnb0
  rwa [hnb]

end IntegrationInACVF.Section3ACVF.RVIntegerSequences
