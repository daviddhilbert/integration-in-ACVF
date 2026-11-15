import Integration7.ActualRVVolumeLiftPresentations
import Integration7.NativeRVGraphVolumeRefinements

/-! Literal native lift charts are genuine full volume bijections and
retain any literal RV density coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def actualRVVolumeLiftChartMap (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) :=
  literalVolumeLiftMap hc U.underlying.obj (actualRVVolumeLiftPresentation hc U.underlying.obj)
    (actual_rv_volume_lift_presents hc U.underlying.obj)

def actualRVVolumeLiftChartObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) : PositiveVFVolumeObject (M := M) S k :=
  nativeMixedVFVolumeObject hc (actualRVVolumeLiftPresentation hc U.underlying.obj)
    (actual_rv_volume_lift_finite_labels hc U) ((rvVolumeLift U).form.pullback (actualRVVolumeLiftChartMap hc U))

def actualRVVolumeLiftChart (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection (actualRVVolumeLiftChartObject hc U) (rvVolumeLift U) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (actualRVVolumeLiftChartMap hc U)
    (literalVolumeLiftMap_bijective hc U.underlying.obj _ (actual_rv_volume_lift_presents hc U.underlying.obj))
    (fun _ => rfl) (fun _ => rfl)

theorem actual_rv_volume_lift_chart_density (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) (δ : Fin U.underlying.obj.arity)
    (hU : ∀ u, U.form.value u = u.val δ) (p : (actualRVVolumeLiftChartObject hc U).domain) :
    (actualRVVolumeLiftChartObject hc U).form.value p = p.val.2 δ := by
  exact hU (liftLabelMap U.underlying.obj (actualRVVolumeLiftChartMap hc U p))

theorem actual_rv_volume_lift_chart_nonzero (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) (δ : Fin U.underlying.obj.arity)
    (hU : ∀ u, U.form.value u = u.val δ) :
    ∀ p : actualRVVolumeLiftPresentation hc U.underlying.obj, (p.val.2 δ).val ≠ iRVZero := by
  intro p
  apply (rv_nonzero_iff_raw _).mp
  intro hz
  exact (actualRVVolumeLiftChartObject hc U).form.nonzero ⟨p.val,p.property⟩
    ((actual_rv_volume_lift_chart_density hc U δ hU ⟨p.val,p.property⟩).trans hz)

end IntegrationInACVF.Section7
