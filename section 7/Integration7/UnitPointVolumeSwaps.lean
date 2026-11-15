import Integration7.LowerDimensionVolumeProductSwaps
import Integration7.BasicVolumeRelationObjects
import Integration7.RVProductDimension

/-! The unit point contributes one volume degree and no RV dimension.
Consequently its actual unsigned swap with any positive object preserves
volume, which will make its class a central localization denominator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

theorem finite_rv_object_dimension_bound (U : RVFiniteObject (M := M) S n) : rvDim U.obj.domain ≤ n :=
  (rvDim_le_iff U.obj.domain n).mpr ⟨n,le_rfl,U.obj.volume,U.property⟩

theorem essential_rv_dimension_le (U : RVFiniteObject (M := M) S (k+1)) :
    rvDim (rvFiniteEssential U).obj.domain ≤ rvDim U.obj.domain := by
  let f : Map (rvFiniteEssential U).obj.domain U.obj.domain := Map.inclusion (rvEssentialLabels_subset U.obj)
  apply rvDim_le_of_finite_map f (Map.finiteFibres_of_injective ?_)
  intro u v h
  exact Subtype.ext (congrArg (fun z : U.obj.domain => z.val) h)

theorem point_product_essential_dimension_lt
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    rvDim (U.prod (degreeOnePointVolumeObject (C.base : Set M))).essential.obj.domain < (k+1)+1 := by
  let P := degreeOnePointVolumeObject (M := M) (C.base : Set M)
  have hP : rvDim P.underlying.obj.domain ≤ 0 := rvDim_le_arity P.underlying.obj.domain
  have hFull : rvDim (U.prod P).underlying.obj.domain ≤ k+1 :=
    (rvDim_productDomain_le U.underlying.obj.domain P.underlying.obj.domain).trans
      (by simpa only [Nat.add_zero] using Nat.add_le_add (finite_rv_object_dimension_bound U.underlying) hP)
  exact Nat.lt_succ_of_le ((essential_rv_dimension_le (U.prod P).underlying).trans hFull)

def volumeUnitPointSwapIso
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.prod (degreeOnePointVolumeObject (C.base : Set M)))
      (unsignedProductSwapObject U (degreeOnePointVolumeObject (C.base : Set M))) :=
  volumeUnsignedProductSwapIsoOfDim C U (degreeOnePointVolumeObject (C.base : Set M))
    (point_product_essential_dimension_lt C U)

end IntegrationInACVF.Section7
