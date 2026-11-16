module

public import Integration7.HKZeroVolumeLifts
public import Section9.MixedJacobian

@[expose] public section

/-! The nonvacuous weighted degree-zero descent needed by Corollary 2.34.
The given lift's actual zero-arity Jacobian is one, and its supplied label
map is retained in the resulting weight-preserving RV isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def zeroVolumeDescentOfDensity {U V : ZeroRVVolumeObject (M := M) S}
    (e : U.underlying ≅ V.underlying) (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hρ : ∀ p, (zeroLift U).form.value p = (zeroLift V).form.value (f p)) : ZeroRVVolumeIso U V where
  iso := e
  density u := by
    let p := (liftLabelMap U.underlying.obj).inverse (zero_lift_label_map_bijective U.underlying.obj) u
    have h := hρ p
    change U.form.value (liftLabelMap U.underlying.obj p) = V.form.value (liftLabelMap V.underlying.obj (f p)) at h
    rw [hlabel] at h
    have hp : liftLabelMap U.underlying.obj p = u := Map.apply_inverse _ _ u
    rw [hp] at h
    exact h

def corollary_2_34_zero_weighted {U V : ZeroRVVolumeObject (M := M) S}
    (e : U.underlying ≅ V.underlying) (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (zeroLift U).form.value p = (zeroLift V).form.value (f p) * CanonicalRV.encodedRv J) :
    ZeroRVVolumeIso U V := by
  apply zeroVolumeDescentOfDensity e f hlabel
  intro p
  obtain ⟨J,hJ,hρ⟩ := hMeasure p
  have he : J = 1 := hJ.unique (hasMixedVFJacobianAt_zero_arity f p)
  rw [he,RVOperations.rv_one,mul_one] at hρ
  exact hρ

@[simp] theorem corollary_2_34_zero_weighted_underlying {U V : ZeroRVVolumeObject (M := M) S}
    (e : U.underlying ≅ V.underlying) (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj))
    (hlabel : ∀ p, liftLabelMap V.underlying.obj (f p) = finiteIsoMap e (liftLabelMap U.underlying.obj p))
    (hMeasure : ∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
      (zeroLift U).form.value p = (zeroLift V).form.value (f p) * CanonicalRV.encodedRv J) :
    (corollary_2_34_zero_weighted e f hlabel hMeasure).iso = e := rfl

end IntegrationInACVF.Section7.HK
