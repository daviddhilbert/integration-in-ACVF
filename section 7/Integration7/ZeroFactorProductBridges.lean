import Integration7.ZeroFactorVolumeIsomorphisms
import Integration7.VolumeIsoDegreeReindex

/-! The concrete zero-factor charts agree with the original all-degree
product, including its unit density convention in ordinary RV[0]. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeProductPositiveZeroIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    RVVolumeIso (rvVolumeProduct (C.base : Set M) (k+1) 0 U Z) (U.prod_zero Z) := by
  let P : PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
    rvVolumeProduct (C.base : Set M) (k+1) 0 U Z
  let E := U.prod_zero Z
  let f : Map P.underlying.obj.domain E.underlying.obj.domain := Map.id _
  have hcoord : ∀ x, E.underlying.obj.value (f x) = P.underlying.obj.value x := fun _ => rfl
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := P.underlying.obj) (V := E.underlying.obj) f Function.bijective_id hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc C e hcoord
  intro x
  change U.form.value _ = U.form.value _ * 1
  exact (mul_one _).symm

def volumeProductZeroPositiveIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (rvVolumeProduct (C.base : Set M) 0 (k+1) Z U)
      ((PositiveRVVolumeObject.zero_prod Z U).reindexDegree (Nat.zero_add k)) := by
  let P : PositiveRVVolumeObject (M := M) (C.base : Set M) (0+k) :=
    rvVolumeProduct (C.base : Set M) 0 (k+1) Z U
  let E := (PositiveRVVolumeObject.zero_prod Z U).reindexDegree (Nat.zero_add k)
  let f : Map P.underlying.obj.domain E.underlying.obj.domain := Map.id _
  have hcoord : ∀ x, E.underlying.obj.value (f x) = P.underlying.obj.value x := by
    intro x
    funext i
    rfl
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := P.underlying.obj) (V := E.underlying.obj) f Function.bijective_id hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc C e hcoord
  intro x
  change U.form.value _ = 1 * U.form.value _
  exact (one_mul _).symm

end IntegrationInACVF.Section7
