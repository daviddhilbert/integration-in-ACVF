module

public import Integration7.UnitPointVolumeSwaps
public import Integration7.GammaPermutedVolumeObjects

@[expose] public section

/-! Below the full RV dimension, unchanged-density coordinate
permutation is an actual volume isomorphism. Multiplication by the
unit point always supplies this strict dimension inequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeCoordinatePermutationIsoOfDim (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (σ : Equiv.Perm (Fin (k+1))) (hd : rvDim U.essential.obj.domain < k+1) :
    RVVolumeIso U (U.permuteVolume σ) := by
  let eFull : U.underlying ≅ (U.permuteVolume σ).underlying :=
    rvFiniteIsoOfAmbient (rvReindexVolumeIso U.underlying.obj σ)
  let e := rvFiniteEssentialIso eFull
  apply RVVolumeIso.of_gamma_product_of_lower_dimension e hd
  · intro u
    rfl
  · intro u
    let u0 : U.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset _ u.property⟩
    change (∏ i,Values.vrv (U.underlying.obj.value u0 i)) =
      ∏ i,Values.vrv (U.underlying.obj.value u0 (σ i))
    exact (Equiv.prod_comp σ (fun i => Values.vrv (U.underlying.obj.value u0 i))).symm

def pointStabilizedVolumePermutationIso (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (σ : Equiv.Perm (Fin ((k+1)+1))) :
    RVVolumeIso (U.prod (degreeOnePointVolumeObject (C.base : Set M)))
      ((U.prod (degreeOnePointVolumeObject (C.base : Set M))).permuteVolume σ) :=
  volumeCoordinatePermutationIsoOfDim C _ σ (point_product_essential_dimension_lt C U)

end IntegrationInACVF.Section7
