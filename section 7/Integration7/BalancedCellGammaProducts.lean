import IntegrationSection4.BalancedSlope

/-! Remark 4.6 gives exactly the equality of the two products of Gamma
volume coordinates in the balanced two-cell comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem balanced_cell_gamma_difference_product
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R f r t) (hr : r ≠ rv (0 : VF (M := M)))
    (x y : VF (M := M)) (hx : x ∈ first R) (hy : y ∈ first R) :
    Values.vfValueHom (f x-f y) * Values.vrv r = Values.vfValueHom (x-y) * Values.vrv t := by
  obtain ⟨hD,hE,hFib,hOO,s,hLin⟩ := h
  have hSlope := BalancedSlope.remark_4_6 hFib hr x hx s hLin
  have hDiff := hLin y x ⟨y,hy,rfl⟩ ⟨x,hx,rfl⟩
  have hfx : (⟨rawMap f x.val,rawMap_vf f (first R) x.val ⟨x,hx,rfl⟩⟩ : VFType (M := M)) = f x :=
    Subtype.ext (rawMap_on f x)
  have hfy : (⟨rawMap f y.val,rawMap_vf f (first R) y.val ⟨y,hy,rfl⟩⟩ : VFType (M := M)) = f y :=
    Subtype.ext (rawMap_on f y)
  change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) =
    s.val * Values.vfValueHom (x-y) at hDiff
  rw [hfx,hfy,hSlope] at hDiff
  have hr0 : Values.vrv r ≠ 0 := by
    intro he
    apply hr
    apply Subtype.ext
    exact ((Values.vrv_eq_infinity_iff r).mp (he.trans Values.infinity_eq_zero.symm)).trans
      ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
  calc
    Values.vfValueHom (f x-f y) * Values.vrv r =
        ((Values.vrv t / Values.vrv r) * Values.vfValueHom (x-y)) * Values.vrv r := by rw [hDiff]
    _ = ((Values.vrv t / Values.vrv r) * Values.vrv r) * Values.vfValueHom (x-y) := by ac_rfl
    _ = Values.vrv t * Values.vfValueHom (x-y) := by rw [div_mul_cancel₀ _ hr0]
    _ = Values.vfValueHom (x-y) * Values.vrv t := mul_comm _ _

end IntegrationInACVF.Section7
