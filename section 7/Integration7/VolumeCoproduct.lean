import Integration7.RVVolumeObjects
import Integration7.VolumeFormGluing
import Section4.RVCoproduct

/-! Tagged coproducts retain the density on each summand. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveRVVolumeObject.coprod (U V : PositiveRVVolumeObject (M := M) S k) :
    PositiveRVVolumeObject (M := M) S k where
  underlying := rvFiniteCoprodObject U.underlying V.underlying
  form := (U.form.pullback (rvUntagLeft U.underlying.obj.domain V.underlying.obj.arity)).union
    (V.form.pullback (rvUntagRight V.underlying.obj.domain U.underlying.obj.arity))

theorem coprod_density_left (U V : PositiveRVVolumeObject (M := M) S k)
    (u : U.underlying.obj.domain) :
    (U.coprod V).form.value (rvCoprodLeftMap U.underlying.obj V.underlying.obj u) =
      U.form.value u := by
  change (((U.form.map.comp (rvUntagLeft U.underlying.obj.domain V.underlying.obj.arity)).union
    (V.form.map.comp (rvUntagRight V.underlying.obj.domain U.underlying.obj.arity)))
      ⟨((rvLeftTagMap U.underlying.obj.domain V.underlying.obj.arity).toImage u).val,
        Or.inl ((rvLeftTagMap U.underlying.obj.domain V.underlying.obj.arity).toImage u).property⟩).val 0 = _
  rw [Map.union_on_left]
  exact congrArg U.form.value (Map.inverse_apply _ _ u)

theorem coprod_density_right (U V : PositiveRVVolumeObject (M := M) S k)
    (v : V.underlying.obj.domain) :
    (U.coprod V).form.value (rvCoprodRightMap U.underlying.obj V.underlying.obj v) =
      V.form.value v := by
  change (((U.form.map.comp (rvUntagLeft U.underlying.obj.domain V.underlying.obj.arity)).union
    (V.form.map.comp (rvUntagRight V.underlying.obj.domain U.underlying.obj.arity)))
      ⟨((rvRightTagMap V.underlying.obj.domain U.underlying.obj.arity).toImage v).val,
        Or.inr ((rvRightTagMap V.underlying.obj.domain U.underlying.obj.arity).toImage v).property⟩).val 0 = _
  rw [Map.union_on_right _ _ (rvTaggedImages_disjoint U.underlying.obj.domain V.underlying.obj.domain)]
  exact congrArg V.form.value (Map.inverse_apply _ _ v)

end IntegrationInACVF.Section7
