import Integration7.GammaAbsoluteValues
import VFAlgClosed

/-! Nonzero parameters in the actual blowup cone can have absolute value
arbitrarily close to one from below. No parameters are added to a base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "RV" => CanonicalRV.RVSort M
local notation "Abs" => MonoidWithZeroHom.ValueGroup₀
  (MonoidWithZeroHom.ofClass (Values.presentationValuation (M := M)))

theorem absolute_square_root (a : Abs) :
    ∃ s : RV, RVOperations.absoluteHom s ^ 2 = a := by
  obtain ⟨x,hx⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (.ofClass (Values.presentationValuation (M := M))) a
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq x (by decide : 0 < (2 : ℕ))
  refine ⟨CanonicalRV.encodedRv y,?_⟩
  rw [RVOperations.absolute_rv]
  let v := MonoidWithZeroHom.ValueGroup₀.restrict₀
    (.ofClass (Values.presentationValuation (M := M)))
  change v y ^ 2 = a
  exact ((map_pow v y 2).symm.trans (congrArg v hy)).trans hx

theorem exists_absolute_cone_factor (a b : Abs) (ha : a ≠ 0) (hab : a < b) :
    ∃ s : RV, s ≠ 0 ∧ RVOperations.absoluteHom s < 1 ∧ a < RVOperations.absoluteHom s * b := by
  have hb : b ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hab)
  have hr0 : a / b ≠ 0 := div_ne_zero ha hb
  have hr1 : a / b < 1 := (div_lt_one₀ (pos_iff_ne_zero.mpr hb)).mpr hab
  obtain ⟨s,hs⟩ := absolute_square_root (a/b)
  have hs0 : RVOperations.absoluteHom s ≠ 0 := by
    intro hz
    exact hr0 (by rw [← hs,hz]; simp)
  have hs1 : RVOperations.absoluteHom s < 1 := by
    by_contra hn
    have hle : 1 ≤ RVOperations.absoluteHom s := le_of_not_gt hn
    have : 1 ≤ RVOperations.absoluteHom s ^ 2 := one_le_pow₀ hle
    exact (not_le_of_gt hr1) (hs ▸ this)
  have hrs : a / b < RVOperations.absoluteHom s := by
    rw [← hs,pow_two]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hs1 (pos_iff_ne_zero.mpr hs0)
  exact ⟨s,(RVOperations.absolute_eq_zero s).not.mp hs0,hs1,
    (div_lt_iff₀ (pos_iff_ne_zero.mpr hb)).mp hrs⟩
end IntegrationInACVF.Section7
