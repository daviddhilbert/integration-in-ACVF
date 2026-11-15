import Integration7.DefinableVolumeClassRescaling
import Integration7.PositiveVolumeClassScalarExtensions

/-! The ordinary RV[0] scalar action also commutes with a definable
density multiplier; its finite factor carries no volume coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def volumeRescaleDefinableZeroProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    RVVolumeIso ((U.prod_zero Z).rescaleDefinable c hDef h0)
      ((U.rescaleDefinable c hDef h0).prod_zero Z) :=
  RVVolumeIso.of_preserving_coordinates_full hc C
    (Iso.refl (U.prod_zero Z).underlying) (fun _ => rfl) (fun _ => rfl)

theorem positive_volume_class_rescale_definable_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0)
    (z : RVVolumeBlowupClasses hc C 0) (u : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassRescaleDefinable hc C c hDef h0 (z • u) =
      z • positiveVolumeClassRescaleDefinable hc C c hDef h0 u := by
  have hRep (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
      (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
      rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U =
        positiveVolumeBlowupClass hc C (U.prod_zero Z) :=
    (ordinary_volume_coefficient_smul_eq_right_product hc C (k := k)
      (rvVolumeBlowupClass hc C (n := 0) Z) (positiveVolumeBlowupClass hc C U)).trans
      (positiveVolumeBlowupClass_iso hc C (volumeProductPositiveZeroIso hc C U Z))
  induction z using Quotient.inductionOn with
  | h Z =>
    induction u using Quotient.inductionOn with
    | h U =>
      exact (congrArg (positiveVolumeClassRescaleDefinable hc C c hDef h0) (hRep Z U)).trans
        ((positiveVolumeBlowupClass_iso hc C (volumeRescaleDefinableZeroProductIso hc C U Z c hDef h0)).trans
          (hRep Z (U.rescaleDefinable c hDef h0)).symm)
end IntegrationInACVF.Section7
