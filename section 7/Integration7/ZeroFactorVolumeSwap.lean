import Integration7.ZeroFactorVolumeObjects
import Integration7.SignedVolumeProductSwap

/-! Swapping an ordinary degree-zero factor retains the positive
coordinates in their original order, and therefore preserves the density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod_zero PositiveRVVolumeObject.zero_prod
  rvFiniteProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volumeZeroProductSwap_coordinates
    (U : PositiveRVVolumeObject (M := M) S k) (Z : RVFiniteObject (M := M) S 0)
    (x : (U.prod_zero Z).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.value
      (rvProductSwapMap U.underlying.obj Z.obj x) = (U.prod_zero Z).underlying.obj.value x := by
  obtain ⟨u,z,rfl⟩ := exists_rvPackPair U.underlying.obj.domain Z.obj.domain x
  rw [rvProductSwapMap_pair,zeroPositiveProduct_coordinates,positiveZeroProduct_coordinates,
    rvUnpack_pair,rvUnpack_pair]
  rfl

theorem volumeZeroProductSwap_density
    (U : PositiveRVVolumeObject (M := M) S k) (Z : RVFiniteObject (M := M) S 0)
    (x : (U.prod_zero Z).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z U).form.value
      (rvProductSwapMap U.underlying.obj Z.obj x) = (U.prod_zero Z).form.value x := by
  obtain ⟨u,z,rfl⟩ := exists_rvPackPair U.underlying.obj.domain Z.obj.domain x
  rw [rvProductSwapMap_pair,zeroPositiveProduct_density,positiveZeroProduct_density,
    rvUnpack_pair,rvUnpack_pair]
  rfl

def volumeZeroProductSwapIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    RVVolumeIso (U.prod_zero Z) (PositiveRVVolumeObject.zero_prod Z U) := by
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := (U.prod_zero Z).underlying.obj) (V := (PositiveRVVolumeObject.zero_prod Z U).underlying.obj)
    (rvProductSwapMap U.underlying.obj Z.obj)
    (rvProductSwapMap_bijective U.underlying.obj Z.obj) (volumeZeroProductSwap_coordinates U Z))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeZeroProductSwap_coordinates U Z) (volumeZeroProductSwap_density U Z)

end IntegrationInACVF.Section7
