module

public import Integration7.OrdinaryVolumeCoefficientExtensions
public import Integration7.BlowupParameterExtension
public import Integration7.IndexedVolumeEmpty

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Enlarging the real parameter base gives an additive map on actual
positive common-blowup classes. The representative and coproduct charts
retain their original RV coordinates and densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def positiveVolumeClassExtend
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (k : ℕ) :
    PositiveVolumeBlowupClasses hc C k →+ PositiveVolumeBlowupClasses hc D k where
  toFun := Quotient.map (fun U => U.extend hCD) (fun _ _ h => h.extend hCD)
  map_zero' := positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_empty hc D _ _ rfl rfl)
  map_add' a b := Quotient.inductionOn₂ a b (fun U V => positiveVolumeBlowupClass_iso hc D
    (RVVolumeIso.of_preserving_coordinates_full hc D
      (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
      (fun _ => rfl) (fun _ => rfl)))

theorem positive_volume_class_extend_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) {k : ℕ}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeClassExtend hc C D hCD k (positiveVolumeBlowupClass hc C U) =
      positiveVolumeBlowupClass hc D (U.extend hCD) := rfl

end IntegrationInACVF.Section7
