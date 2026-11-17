module

public import Integration7.DefinableVolumeClassRescaling
public import Integration7.PositiveVolumeClassProductExtensions
public import Integration7.VolumeProductPointwise

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Definable density rescaling commutes with multiplication by a
positive constant volume coefficient, on actual products and their classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def volumeRescaleDefinableProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    RVVolumeIso ((U.prod V).rescaleDefinable c hDef h0)
      (U.prod (V.rescaleDefinable c hDef h0)) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := (U.prod V).rescaleDefinable c hDef h0)
    (V := U.prod (V.rescaleDefinable c hDef h0)) (Iso.refl (U.prod V).underlying)
    (fun _ => rfl)
  intro x
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain x
  exact (positiveProduct_density_pair U (V.rescaleDefinable c hDef h0) u v).trans
    ((mul_left_comm (U.form.value u) c (V.form.value v)).trans
      (congrArg (fun t => c*t) (positiveProduct_density_pair U V u v).symm))

theorem positive_volume_class_rescale_definable_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (c : RV) (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0)
    (u : PositiveVolumeBlowupClasses hc C p) (v : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassRescaleDefinable hc C c hDef h0
      (rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u v) =
    rvVolumeBlowupClassesProduct hc C (p+1) (k+1) u
      (positiveVolumeClassRescaleDefinable hc C c hDef h0 v) :=
  Quotient.inductionOn₂ u v (fun U V =>
    positiveVolumeBlowupClass_iso hc C (volumeRescaleDefinableProductIso hc C U V c hDef h0))
end IntegrationInACVF.Section7
