import Integration7.GradedVolumeProducts
import Section4.RVProductAssociativity

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

theorem positiveProduct_density_pair
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (u : U.underlying.obj.domain) (v : V.underlying.obj.domain) :
    (U.prod V).form.value (rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v) =
      U.form.value u * V.form.value v := by
  change (U.form.prod V.form).value (rvUnpack U.underlying.obj.domain V.underlying.obj.domain
    (rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v)) = _
  rw [rvUnpack_pair]
  rfl

theorem positiveProduct_coordinates_pair
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (u : U.underlying.obj.domain) (v : V.underlying.obj.domain) :
    (U.prod V).underlying.obj.value (rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v) =
      rvAppend (U.underlying.obj.value u) (V.underlying.obj.value v) :=
  rvProductObject_value_pair U.underlying.obj V.underlying.obj u v

end IntegrationInACVF.Section7
