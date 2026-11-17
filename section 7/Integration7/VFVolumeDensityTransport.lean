module

public import Integration7.MixedJacobianDensityForms
public import Integration7.VolumeFormScalarArithmetic
public import Integration7.VFVolumeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Any actual mixed definable bijection transports an arbitrary
nonzero density. The Jacobian equation is proved almost everywhere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b k : ℕ}

def transportedVFVolumeForm
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) : VolumeForm B :=
  (ω.div (mixedJacobianDensityForm f)).pullback (f.inverse hf)

theorem transported_vf_volume_form_value
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) (p : A) :
    (transportedVFVolumeForm f hf ω).value (f p) =
      ω.value p / (mixedJacobianDensityForm f).value p := by
  change (ω.div (mixedJacobianDensityForm f)).value (f.inverse hf (f p)) = _
  rw [Map.inverse_apply,VolumeForm.div_value]

theorem preserves_transported_vf_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) :
    PreservesVFVolume ω (transportedVFVolumeForm f hf ω) f := by
  apply (mixed_bijective_jacobian_density_ae hc C hn f hf).mono
  rintro p ⟨J,hJ,hJ0,hValue⟩
  refine ⟨J,hJ,?_⟩
  rw [transported_vf_volume_form_value,← hValue]
  exact (div_mul_cancel₀ _ ((mixedJacobianDensityForm f).value_ne_zero p)).symm

def PositiveVFVolumeObject.transportDensity
    (U V : PositiveVFVolumeObject (M := M) S k) (f : Map U.domain V.domain)
    (hf : Function.Bijective f) : PositiveVFVolumeObject (M := M) S k where
  arity := V.arity
  domain := V.domain
  finite_labels := V.finite_labels
  form := transportedVFVolumeForm f hf U.form

def transportedVFVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (f : Map U.domain V.domain) (hf : Function.Bijective f) :
    VFVolumeBijection U (U.transportDensity V f hf) :=
  ⟨f,hf,preserves_transported_vf_volume hc C (Nat.zero_lt_succ k) f hf U.form⟩

end IntegrationInACVF.Section7
