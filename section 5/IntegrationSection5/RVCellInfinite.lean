import IntegrationSection5.UnaryCellZeros

/-! Infinitude of each nonzero actual RV class. Powers of a nonzero
strictly small element give an explicit injective sequence in the class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nonzero_rv_class_infinite (x : VF (M := M)) (hx : x ≠ 0) :
    ({y : VF (M := M) | rv y = rv x} : Set (VF (M := M))).Infinite := by
  obtain ⟨ε,hε0,hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hεv : v ε < 1 := by
    have h := (not_congr (hv 1 ε)).mp hε
    simpa only [map_one] using lt_of_not_ge h
  have hεpos : 0 < v ε := zero_lt_iff.mpr ((v.ne_zero_iff).mpr hε0)
  let f : ℕ → VF (M := M) := fun k => x+x*ε^(k+1)
  have hf : Function.Injective f := by
    intro i j hij
    have hp : ε^(i+1) = ε^(j+1) := mul_left_cancel₀ hx (add_left_cancel hij)
    have hvp : (v ε)^(i+1) = (v ε)^(j+1) := by
      simpa only [map_pow] using congrArg v hp
    exact Nat.add_right_cancel ((pow_right_strictAnti₀ hεpos hεv).injective hvp)
  have hmem (k : ℕ) : rv (f k) = rv x := by
    have hp : (v ε)^(k+1) < 1 := by
      simpa only [pow_zero] using (pow_right_strictAnti₀ hεpos hεv) (Nat.zero_lt_succ k)
    have hclose : v (f k-x) < v x := by
      change v (x+x*ε^(k+1)-x) < v x
      rw [add_sub_cancel_left,map_mul,map_pow]
      simpa only [mul_one] using mul_lt_mul_of_pos_left hp (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hx))
    exact Subtype.ext (Balls.rv_eq_of_sub_lt v hv (f k) x hx hclose)
  exact (Set.infinite_range_of_injective hf).mono (by rintro y ⟨k,rfl⟩; exact hmem k)

end IntegrationInACVF.Section5
