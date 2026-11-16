import Integration7.HKRVVolumeObjects
import Integration7.NondegenerateFiniteIso

/-! Exact RV-weight preservation at zero. No almost-everywhere predicate
or vacuous zero-dimensional exception is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

structure ZeroRVVolumeIso (U V : ZeroRVVolumeObject (M := M) S) where
  iso : U.underlying ≅ V.underlying
  density : ∀ u, U.form.value u = V.form.value (finiteIsoMap iso u)

def ZeroRVVolumeIso.refl (U : ZeroRVVolumeObject (M := M) S) : ZeroRVVolumeIso U U :=
  ⟨Iso.refl _, fun _ => rfl⟩

def ZeroRVVolumeIso.trans {U V W : ZeroRVVolumeObject (M := M) S}
    (f : ZeroRVVolumeIso U V) (g : ZeroRVVolumeIso V W) : ZeroRVVolumeIso U W where
  iso := f.iso.trans g.iso
  density u := (f.density u).trans (g.density (finiteIsoMap f.iso u))

def ZeroRVVolumeIso.symm {U V : ZeroRVVolumeObject (M := M) S}
    (f : ZeroRVVolumeIso U V) : ZeroRVVolumeIso V U where
  iso := f.iso.symm
  density v := by
    have h := f.density (finiteIsoMap f.iso.symm v)
    have he : finiteIsoMap f.iso (finiteIsoMap f.iso.symm v) = v :=
      SpecialTransformations.Section7.rvIso_inv_apply ((finiteVolumeProperty S 0).ι.mapIso f.iso).symm v
    rw [he] at h
    exact h.symm

def ZeroRVVolumeIso.ofBijection {U V : ZeroRVVolumeObject (M := M) S}
    (f : Map U.underlying.obj.domain V.underlying.obj.domain) (hf : Function.Bijective f)
    (hω : ∀ u, U.form.value u = V.form.value (f u)) : ZeroRVVolumeIso U V :=
  ⟨finiteIsoOfNondegenerateBijection f hf (fun _ i => i.elim0) (fun _ i => i.elim0), hω⟩

def ZeroRVVolumeIso.unitForm {U V : RVFiniteObject (M := M) S 0} (e : U ≅ V) :
    ZeroRVVolumeIso (ZeroRVVolumeObject.unitForm U) (ZeroRVVolumeObject.unitForm V) :=
  ⟨e, fun _ => rfl⟩

theorem zero_unit_form_iso_iff (U V : RVFiniteObject (M := M) S 0) :
    Nonempty (ZeroRVVolumeIso (ZeroRVVolumeObject.unitForm U) (ZeroRVVolumeObject.unitForm V)) ↔
      Nonempty (U ≅ V) :=
  ⟨fun ⟨e⟩ => ⟨e.iso⟩, fun ⟨e⟩ => ⟨ZeroRVVolumeIso.unitForm e⟩⟩

def rvVolumeIsoInDegree (S : Set M) : (n : ℕ) →
    RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n → Type
  | 0, U, V => ZeroRVVolumeIso U V
  | _+1, U, V => RVVolumeIso U V

def zeroRVVolumeSetoid (S : Set M) : Setoid (ZeroRVVolumeObject (M := M) S) where
  r U V := Nonempty (ZeroRVVolumeIso U V)
  iseqv := ⟨fun U => ⟨ZeroRVVolumeIso.refl U⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev ZeroRVVolumeClasses (S : Set M) := Quotient (zeroRVVolumeSetoid (M := M) S)

end IntegrationInACVF.Section7.HK
