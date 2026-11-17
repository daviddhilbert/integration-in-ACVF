module

public import Integration7.HKZeroVFVolumeObjects
public import Integration7.OrdinaryZeroLiftIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The corrected zero lift preserves and reflects the exact RV form.
The ordinary lift-label projection supplies the actual definable inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroLift (U : ZeroRVVolumeObject (M := M) S) : ZeroVFVolumeObject (M := M) S where
  underlying := rvLiftFiniteObject (rawRVSpace (M := M) 1) U.underlying
  form := U.form.pullback (liftLabelMap U.underlying.obj)

@[simp] theorem zeroLift_density (U : ZeroRVVolumeObject (M := M) S)
    (p : rvLift U.underlying.obj) : (zeroLift U).form.value p = U.form.value (liftLabelMap U.underlying.obj p) := rfl

def zeroLiftIso {U V : ZeroRVVolumeObject (M := M) S} (e : ZeroRVVolumeIso U V) :
    ZeroVFVolumeIso (zeroLift U) (zeroLift V) where
  iso := ordinaryZeroLiftIsoOfRVIso e.iso
  density p := by
    change U.form.value (liftLabelMap U.underlying.obj p) =
      V.form.value (liftLabelMap V.underlying.obj
        ((liftLabelMap V.underlying.obj).inverse (zero_lift_label_map_bijective V.underlying.obj)
          (finiteIsoMap e.iso (liftLabelMap U.underlying.obj p))))
    rw [Map.apply_inverse]
    exact e.density _

def zeroRVOfLiftIso {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroVFVolumeIso (zeroLift U) (zeroLift V)) : ZeroRVVolumeIso U V where
  iso := ordinaryRVIsoOfZeroLiftIso e.iso
  density u := by
    let p := (liftLabelMap U.underlying.obj).inverse (zero_lift_label_map_bijective U.underlying.obj) u
    have h := e.density p
    change U.form.value (liftLabelMap U.underlying.obj p) =
      V.form.value (liftLabelMap V.underlying.obj (finiteZeroVFMap e.iso p)) at h
    change U.form.value u = V.form.value (liftLabelMap V.underlying.obj (finiteZeroVFMap e.iso p))
    have hp : liftLabelMap U.underlying.obj p = u := Map.apply_inverse _ _ u
    rw [hp] at h
    exact h

theorem zero_lift_iso_iff (U V : ZeroRVVolumeObject (M := M) S) :
    Nonempty (ZeroVFVolumeIso (zeroLift U) (zeroLift V)) ↔ Nonempty (ZeroRVVolumeIso U V) :=
  ⟨fun ⟨e⟩ => ⟨zeroRVOfLiftIso e⟩,fun ⟨e⟩ => ⟨zeroLiftIso e⟩⟩

end IntegrationInACVF.Section7.HK
