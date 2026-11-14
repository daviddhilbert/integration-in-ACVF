import Integration7.UniformVolumeData
import Integration7.VolumeRelabeling
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeDataRelabelIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (D E : RVVolumeData (M := M) (C.base : Set M) n)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u) :
    RVVolumeIsoInDegree (C.base : Set M) n D.toObject E.toObject := by
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := D.underlying.obj) (V := E.underlying.obj) F hF hcoord)
  cases n with
  | zero => exact e
  | succ n =>
    exact RVVolumeIso.of_preserving_coordinates_full hc C
      (U := D.toObject) (V := E.toObject) e hcoord hφ

def rvVolumeDataReindexedIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (h : n=m) (D : RVVolumeData (M := M) (C.base : Set M) n)
    (E : RVVolumeData (M := M) (C.base : Set M) m)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) ∘ finCongr h = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u) :
    RVVolumeIsoInDegree (C.base : Set M) n D.toObject (h.symm ▸ E.toObject) := by
  cases h
  exact rvVolumeDataRelabelIso hc C D E F hF hcoord hφ

end IntegrationInACVF.Section7
