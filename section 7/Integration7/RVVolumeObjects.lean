import Integration7.VolumeForms
import Section9.RVFiniteEssential

/-! Finite-volume RV objects with an actual nonzero definable density.
Degree zero retains the ordinary RV[0] convention. -/

noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

structure PositiveRVVolumeObject (S : Set M) (k : ℕ) where
  underlying : RVFiniteObject (M := M) S (k + 1)
  form : VolumeForm underlying.obj.domain

abbrev RVVolumeObject (S : Set M) : ℕ → Type
  | 0 => RVFiniteObject (M := M) S 0
  | k + 1 => PositiveRVVolumeObject (M := M) S k

namespace PositiveRVVolumeObject

def essential (U : PositiveRVVolumeObject (M := M) S k) :
    RVFiniteObject (M := M) S (k + 1) := rvFiniteEssential U.underlying

def essentialForm (U : PositiveRVVolumeObject (M := M) S k) :
    VolumeForm U.essential.obj.domain :=
  U.form.restrict (rvEssentialLabels_subset U.underlying.obj)

theorem essential_nonzero (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) (i : Fin (k + 1)) :
    (U.essential.obj.value u i).val ≠ iRVZero :=
  rvEssential_value_nonzero U.underlying.obj u i

theorem essentialForm_nonzero (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : U.essentialForm.value u ≠ 0 :=
  U.essentialForm.nonzero u

def restrict (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (h : A.carrier ⊆ U.underlying.obj.domain.carrier) : PositiveRVVolumeObject (M := M) S k where
  underlying := rvFiniteRestrict U.underlying A h
  form := U.form.restrict h

@[simp] theorem restrict_density (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (h : A.carrier ⊆ U.underlying.obj.domain.carrier) (a : A) :
    (U.restrict A h).form.value a = U.form.value ⟨a.val, h a.property⟩ := rfl

end PositiveRVVolumeObject

end IntegrationInACVF.Section7
