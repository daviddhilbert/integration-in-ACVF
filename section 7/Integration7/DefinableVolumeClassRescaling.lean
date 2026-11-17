module

public import Integration7.DefinableDensityRescaling
public import Integration7.VolumeBlowupClasses
public import Integration7.IndexedVolumeEmpty

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A definable nonzero density multiplier acts additively on actual
common-blowup classes; the coproduct comparison preserves every coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def volumeRescaleDefinableCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    RVVolumeIso ((U.coprod V).rescaleDefinable c hDef h0)
      ((U.rescaleDefinable c hDef h0).coprod (V.rescaleDefinable c hDef h0)) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := (U.coprod V).rescaleDefinable c hDef h0)
    (V := (U.rescaleDefinable c hDef h0).coprod (V.rescaleDefinable c hDef h0))
    (Iso.refl (U.coprod V).underlying)
  · intro x; rfl
  · intro x
    rcases volumeCoprod_cases U V x with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exact (coprod_density_left (U.rescaleDefinable c hDef h0)
        (V.rescaleDefinable c hDef h0) u).trans
        (congrArg (fun t => c * t) (coprod_density_left U V u)).symm
    · exact (coprod_density_right (U.rescaleDefinable c hDef h0)
        (V.rescaleDefinable c hDef h0) v).trans
        (congrArg (fun t => c * t) (coprod_density_right U V v)).symm

def positiveVolumeClassRescaleDefinable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    PositiveVolumeBlowupClasses hc C k →+ PositiveVolumeBlowupClasses hc C k where
  toFun := Quotient.map (fun U => U.rescaleDefinable c hDef h0)
    (fun _ _ h => h.rescale_definable hc C c hDef h0)
  map_zero' := positiveVolumeBlowupClass_iso hc C (RVVolumeIso.of_empty hc C _ _ rfl rfl)
  map_add' u v := Quotient.inductionOn₂ u v (fun U V =>
    positiveVolumeBlowupClass_iso hc C (volumeRescaleDefinableCoprodIso hc C U V c hDef h0))

theorem positive_volume_class_rescale_definable_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeClassRescaleDefinable hc C c hDef h0 (positiveVolumeBlowupClass hc C U) =
      positiveVolumeBlowupClass hc C (U.rescaleDefinable c hDef h0) := rfl
end IntegrationInACVF.Section7
