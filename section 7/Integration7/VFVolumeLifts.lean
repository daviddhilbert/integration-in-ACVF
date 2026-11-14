import Integration7.VFVolumeObjects
import Integration7.RVVolumeObjects
import Integration7.VolumeCoproductUnits
import Section9.LiftLabelRepresentatives
import Section4.GradedLifts

/-! Actual volume lifts. The constructions and empty-domain statement
are recovered from the original recorded module; scissors classes will
be added after their genuine equivalence relation is reconstructed. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
noncomputable section

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def rvVolumeLift (U : PositiveRVVolumeObject (M := M) S k) :
    PositiveVFVolumeObject (M := M) S k where
  arity := U.underlying.obj.arity
  domain := rvLift U.underlying.obj
  finite_labels := rvLift_finite_rv_fibres U.underlying.obj U.underlying.property
  form := U.form.pullback (liftLabelMap U.underlying.obj)

@[simp] theorem rvVolumeLift_density (U : PositiveRVVolumeObject (M := M) S k)
    (p : (rvVolumeLift U).domain) :
    (rvVolumeLift U).form.value p = U.form.value (liftLabelMap U.underlying.obj p) := rfl

def rvVolumeLiftOfDegree (S : Set M) :
    (n : ℕ) → RVVolumeObject (M := M) S n → VFVolumeObject (M := M) S n
  | 0, U => rvLiftFiniteObject (rawRVSpace (M := M) 1) U
  | _ + 1, U => rvVolumeLift U

theorem rvVolumeLift_empty_domain (S : Set M) (k : ℕ) :
    (rvVolumeLift (PositiveRVVolumeObject.empty (M := M) S k)).domain.carrier = ∅ :=
  rvLift_empty_of_domain_empty _ rfl

end IntegrationInACVF.Section7
