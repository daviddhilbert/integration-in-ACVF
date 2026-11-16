import Integration7.HKMixedVolumeIsomorphisms
import Integration7.VolumeIsoDegreeReindex

/-! The specialized weighted scalar products agree with the genuine
all-degree Cartesian product, including their actual forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def productPositiveZeroIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    RVVolumeIso (product (C.base : Set M) (k+1) 0 U Z) (positiveZeroProduct U Z) := by
  let P : PositiveRVVolumeObject (M := M) (C.base : Set M) k := product (C.base : Set M) (k+1) 0 U Z
  let E := positiveZeroProduct U Z
  let f : Map P.underlying.obj.domain E.underlying.obj.domain := Map.id _
  have hcoord : ∀ x, E.underlying.obj.value (f x) = P.underlying.obj.value x := fun _ => rfl
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := P.underlying.obj) (V := E.underlying.obj) f Function.bijective_id hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc C e hcoord
  intro x
  change Z.form.value _ * U.form.value _ = U.form.value _ * Z.form.value _
  exact mul_comm _ _

def productZeroPositiveIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (product (C.base : Set M) 0 (k+1) Z U) ((zeroProduct Z U).reindexDegree (Nat.zero_add k)) := by
  let P : PositiveRVVolumeObject (M := M) (C.base : Set M) (0+k) := product (C.base : Set M) 0 (k+1) Z U
  let E := (zeroProduct Z U).reindexDegree (Nat.zero_add k)
  let f : Map P.underlying.obj.domain E.underlying.obj.domain := Map.id _
  have hcoord : ∀ x, E.underlying.obj.value (f x) = P.underlying.obj.value x := by
    intro x
    funext i
    rfl
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := P.underlying.obj) (V := E.underlying.obj) f Function.bijective_id hcoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hcoord (fun _ => rfl)

end IntegrationInACVF.Section7.HK
