import Integration7.HKZeroDefinableDensityRescaling
import Integration7.HKNativeZeroCoefficientFieldIntegrals
import Integration7.DefinableVolumeClassRescaling

/-! Definable Jacobian density multipliers commute with genuine
weighted products in all zero/positive combinations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (c : CanonicalRV.RVSort M) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0)

def zeroVolumeClassRescaleDefinable : RVBlowupClasses hc C 0 → RVBlowupClasses hc C 0 :=
  Quotient.map (fun Z => Z.rescaleDefinable c hDef h0)
    (fun _ _ ⟨e⟩ => ⟨e.rescaleDefinable c hDef h0⟩)

def weightedZeroProductRescaleRightIso
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso ((zeroProduct Z U).rescaleDefinable c hDef h0)
      (zeroProduct Z (U.rescaleDefinable c hDef h0)) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := (zeroProduct Z U).rescaleDefinable c hDef h0)
    (V := zeroProduct Z (U.rescaleDefinable c hDef h0)) (Iso.refl _)
    (fun _ => rfl)
  intro q
  change Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q)) *
    (c * U.form.value (Map.prodSnd _ _ (rvUnpack _ _ q))) =
    c * (Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q)) * U.form.value (Map.prodSnd _ _ (rvUnpack _ _ q)))
  exact mul_left_comm _ _ _

def weightedZeroProductRescaleLeftIso
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso ((zeroProduct Z U).rescaleDefinable c hDef h0)
      (zeroProduct (Z.rescaleDefinable c hDef h0) U) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := (zeroProduct Z U).rescaleDefinable c hDef h0)
    (V := zeroProduct (Z.rescaleDefinable c hDef h0) U) (Iso.refl _)
    (fun _ => rfl)
  intro q
  change (c * Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q))) *
      U.form.value (Map.prodSnd _ _ (rvUnpack _ _ q)) =
    c * (Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q)) * U.form.value (Map.prodSnd _ _ (rvUnpack _ _ q)))
  exact mul_assoc _ _ _

theorem positive_rescale_weighted_smul_right
    (z : RVBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassRescaleDefinable hc C c hDef h0 (z • u) =
      z • positiveVolumeClassRescaleDefinable hc C c hDef h0 u := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction u using Quotient.inductionOn with
    | h U =>
      exact (congrArg (positiveVolumeClassRescaleDefinable hc C c hDef h0)
        (weighted_zero_smul_representative hc C Z U)).trans
        ((positiveVolumeBlowupClass_iso hc C (weightedZeroProductRescaleRightIso hc C c hDef h0 Z U)).trans
          (weighted_zero_smul_representative hc C Z (U.rescaleDefinable c hDef h0)).symm)

theorem positive_rescale_weighted_smul_left
    (z : RVBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassRescaleDefinable hc C c hDef h0 (z • u) =
      zeroVolumeClassRescaleDefinable hc C c hDef h0 z • u := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction u using Quotient.inductionOn with
    | h U =>
      exact (congrArg (positiveVolumeClassRescaleDefinable hc C c hDef h0)
        (weighted_zero_smul_representative hc C Z U)).trans
        ((positiveVolumeBlowupClass_iso hc C (weightedZeroProductRescaleLeftIso hc C c hDef h0 Z U)).trans
          (weighted_zero_smul_representative hc C (Z.rescaleDefinable c hDef h0) U).symm)

theorem zero_rescale_product_right (z t : RVBlowupClasses hc C 0) :
    zeroVolumeClassRescaleDefinable hc C c hDef h0 (z*t) =
      z * zeroVolumeClassRescaleDefinable hc C c hDef h0 t := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction t using Quotient.inductionOn with
    | h T =>
      apply Quotient.sound
      refine ⟨ZeroRVVolumeIso.ofBijection (Map.id _) Function.bijective_id ?_⟩
      intro q
      change c * (Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q)) * T.form.value (Map.prodSnd _ _ (rvUnpack _ _ q))) =
        Z.form.value (Map.prodFst _ _ (rvUnpack _ _ q)) * (c*T.form.value (Map.prodSnd _ _ (rvUnpack _ _ q)))
      exact mul_left_comm _ _ _

end IntegrationInACVF.Section7.HK
