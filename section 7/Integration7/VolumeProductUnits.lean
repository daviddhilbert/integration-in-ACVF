import Integration7.ZeroFactorVolumeSwap
import Section4.RVProductUnits
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeProductRightUnitIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.prod_zero (rvFiniteUnitObject (C.base : Set M))) U := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := U.prod_zero (rvFiniteUnitObject (C.base : Set M))) (V := U)
    (rvFiniteIsoOfAmbient (rvProductRightUnitIso U.underlying.obj))
  · intro w
    exact (positiveZeroProduct_coordinates U (rvFiniteUnitObject (C.base : Set M)) w).symm
  · intro _
    rfl

def volumeProductLeftUnitIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (PositiveRVVolumeObject.zero_prod (rvFiniteUnitObject (C.base : Set M)) U) U :=
  ((volumeZeroProductSwapIso hc C U (rvFiniteUnitObject (C.base : Set M))).symm hc C).trans hc C
    (volumeProductRightUnitIso hc C U)
end IntegrationInACVF.Section7
