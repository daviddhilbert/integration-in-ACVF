import Integration7.HKZeroVolumeLifts
import Integration7.OrdinaryFiniteLiftSurjectivity

/-! Every weighted zero VF object has a same-base weighted zero RV lift
presentation. The form is transported through the actual ordinary
presentation; no section of the RV map or density-forgetting step occurs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_volume_lift_presentation_exists (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    ∃ U : ZeroRVVolumeObject (M := M) (C.base : Set M), Nonempty (ZeroVFVolumeIso A (zeroLift U)) := by
  obtain ⟨U,⟨e⟩⟩ := ordinary_finite_lift_presentation_exists hc C A.underlying
  let ρ := A.form.pullback ((finiteZeroVFMap e.symm).comp
    ((liftLabelMap U.obj).inverse (zero_lift_label_map_bijective U.obj)))
  let Z : ZeroRVVolumeObject (M := M) (C.base : Set M) := ⟨U,ρ⟩
  refine ⟨Z,⟨⟨e,?_⟩⟩⟩
  intro a
  change A.form.value a = A.form.value (finiteZeroVFMap e.symm
    ((liftLabelMap U.obj).inverse (zero_lift_label_map_bijective U.obj)
      (liftLabelMap U.obj (finiteZeroVFMap e a))))
  rw [Map.inverse_apply, finiteZeroVFMap_symm_apply]

end IntegrationInACVF.Section7.HK
