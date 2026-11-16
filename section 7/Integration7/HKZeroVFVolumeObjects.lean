module

public import Integration7.HKZeroRVVolumeIsomorphisms
public import Integration7.VFVolumeObjects

@[expose] public section

/-! The sequel's weighted zero VF presentation retains every ordinary
zero-dimensional finite object, with its full definable RV-valued form.
Exact weight-preserving maps replace the legacy vacuous zero equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def finiteZeroVFMap {A B : VFFiniteObject (rawRVSpace (M := M) 1) S 0} (e : A ≅ B) :
    Map A.obj.obj.set B.obj.obj.set :=
  ((vfDimensionProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso
    ((vfBoundedFiniteProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso e)).hom

theorem finiteZeroVFMap_symm_apply {A B : VFFiniteObject (rawRVSpace (M := M) 1) S 0}
    (e : A ≅ B) (a : A.obj.obj.set) : finiteZeroVFMap e.symm (finiteZeroVFMap e a) = a := by
  let E := (vfDimensionProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso
    ((vfBoundedFiniteProperty (rawRVSpace (M := M) 1) S 0).ι.mapIso e)
  exact congrArg (fun f : A.obj.obj ⟶ A.obj.obj => DefinableSetCat.homFunction f a) E.hom_inv_id

theorem finiteZeroVFMap_apply_symm {A B : VFFiniteObject (rawRVSpace (M := M) 1) S 0}
    (e : A ≅ B) (b : B.obj.obj.set) : finiteZeroVFMap e (finiteZeroVFMap e.symm b) = b :=
  finiteZeroVFMap_symm_apply e.symm b

structure ZeroVFVolumeObject (S : Set M) where
  underlying : VFFiniteObject (rawRVSpace (M := M) 1) S 0
  form : VolumeForm underlying.obj.obj.set

structure ZeroVFVolumeIso (A B : ZeroVFVolumeObject (M := M) S) where
  iso : A.underlying ≅ B.underlying
  density : ∀ a, A.form.value a = B.form.value (finiteZeroVFMap iso a)

def ZeroVFVolumeIso.refl (A : ZeroVFVolumeObject (M := M) S) : ZeroVFVolumeIso A A :=
  ⟨Iso.refl _,fun _ => rfl⟩

def ZeroVFVolumeIso.trans {A B D : ZeroVFVolumeObject (M := M) S}
    (f : ZeroVFVolumeIso A B) (g : ZeroVFVolumeIso B D) : ZeroVFVolumeIso A D :=
  ⟨f.iso.trans g.iso,fun a => (f.density a).trans (g.density (finiteZeroVFMap f.iso a))⟩

def ZeroVFVolumeIso.symm {A B : ZeroVFVolumeObject (M := M) S}
    (f : ZeroVFVolumeIso A B) : ZeroVFVolumeIso B A where
  iso := f.iso.symm
  density b := by
    have h := f.density (finiteZeroVFMap f.iso.symm b)
    rw [finiteZeroVFMap_apply_symm] at h
    exact h.symm

def zeroVFVolumeSetoid (S : Set M) : Setoid (ZeroVFVolumeObject (M := M) S) where
  r A B := Nonempty (ZeroVFVolumeIso A B)
  iseqv := ⟨fun A => ⟨ZeroVFVolumeIso.refl A⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev ZeroVFVolumeClasses (S : Set M) := Quotient (zeroVFVolumeSetoid (M := M) S)

end IntegrationInACVF.Section7.HK
