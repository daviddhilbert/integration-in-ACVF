import Integration7.VolumeForms
import Section4.VFCategories

/-! Positive-degree VF objects carry an actual mixed definable domain,
finite RV fibres, and a nonzero definable RV density. Degree zero keeps
the ordinary VF[0] category. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure PositiveVFVolumeObject (S : Set M) (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawMixedSpace (M := M) (k + 1) arity) S
  finite_labels : ∀ x : Fin (k + 1) → VFType (M := M),
    {r : Fin arity → CanonicalRV.RVSort M | (x, r) ∈ domain.carrier}.Finite
  form : VolumeForm domain

abbrev VFVolumeObject (S : Set M) : ℕ → Type
  | 0 => VFFiniteObject (rawRVSpace (M := M) 1) S 0
  | k + 1 => PositiveVFVolumeObject (M := M) S k

def PositiveVFVolumeObject.underlying (U : PositiveVFVolumeObject (M := M) S k) :
    VFFiniteObject (rawRVSpace (M := M) 1) S (k + 1) :=
  ⟨⟨⟨(k + 1, U.arity), U.domain⟩, vfDim_le_arity _ U.domain⟩, U.finite_labels⟩

def PositiveVFVolumeObject.restrict (U : PositiveVFVolumeObject (M := M) S k)
    (A : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) : PositiveVFVolumeObject (M := M) S k where
  arity := U.arity
  domain := A
  finite_labels x := (U.finite_labels x).subset (fun _ hr => hA hr)
  form := U.form.restrict hA

@[simp] theorem PositiveVFVolumeObject.restrict_density
    (U : PositiveVFVolumeObject (M := M) S k)
    (A : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier) (a : A) :
    (U.restrict A hA).form.value a = U.form.value ⟨a.val, hA a.property⟩ := rfl

end IntegrationInACVF.Section7
