module

public import Integration7.PositiveVolumeClassExtensions
public import Integration7.HKVolumeBlowupSemiring

@[expose] public section

/-! Actual positive coefficient products commute with real parameter
extension. The literal RV product chart has the same coordinates and
density on both sides. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem positive_volume_class_extend_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) {p q : ℕ}
    (u : PositiveVolumeBlowupClasses hc C p) (v : PositiveVolumeBlowupClasses hc C q) :
    positiveVolumeClassExtend hc C D hCD ((p+1)+q)
      (rvVolumeBlowupClassesProduct hc C (p+1) (q+1) u v) =
      rvVolumeBlowupClassesProduct hc D (p+1) (q+1)
        (positiveVolumeClassExtend hc C D hCD p u) (positiveVolumeClassExtend hc C D hCD q v) :=
  Quotient.inductionOn₂ u v (fun U V => positiveVolumeBlowupClass_iso hc D
    (RVVolumeIso.of_preserving_coordinates_full hc D
      (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
      (fun _ => rfl) (fun _ => rfl)))

end IntegrationInACVF.Section7.HK
