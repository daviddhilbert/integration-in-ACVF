import Integration7.AllDegreeVolumeData
import Integration7.AllDegreeVolumeCoproducts

/-! Actual coproducts of density-bearing data, before the ordinary
degree-zero object forgets its auxiliary density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def RVVolumeData.coprod (D E : RVVolumeData (M := M) S n) : RVVolumeData (M := M) S n where
  underlying := rvFiniteCoprodObject D.underlying E.underlying
  form := (D.form.pullback (rvUntagLeft D.underlying.obj.domain E.underlying.obj.arity)).union
    (E.form.pullback (rvUntagRight E.underlying.obj.domain D.underlying.obj.arity))

@[simp] theorem RVVolumeData.coprod_toObject (D E : RVVolumeData (M := M) S n) :
    (D.coprod E).toObject = rvVolumeCoprod S n D.toObject E.toObject := by cases n <;> rfl

theorem RVVolumeData.coprod_density_left (D E : RVVolumeData (M := M) S n)
    (u : D.underlying.obj.domain) :
    (D.coprod E).form.value (rvCoprodLeftMap D.underlying.obj E.underlying.obj u) = D.form.value u := by
  change (((D.form.map.comp (rvUntagLeft D.underlying.obj.domain E.underlying.obj.arity)).union
    (E.form.map.comp (rvUntagRight E.underlying.obj.domain D.underlying.obj.arity)))
      ⟨((rvLeftTagMap D.underlying.obj.domain E.underlying.obj.arity).toImage u).val,
        Or.inl ((rvLeftTagMap D.underlying.obj.domain E.underlying.obj.arity).toImage u).property⟩).val 0 = _
  rw [Map.union_on_left]
  exact congrArg D.form.value (Map.inverse_apply _ _ u)

theorem RVVolumeData.coprod_density_right (D E : RVVolumeData (M := M) S n)
    (v : E.underlying.obj.domain) :
    (D.coprod E).form.value (rvCoprodRightMap D.underlying.obj E.underlying.obj v) = E.form.value v := by
  change (((D.form.map.comp (rvUntagLeft D.underlying.obj.domain E.underlying.obj.arity)).union
    (E.form.map.comp (rvUntagRight E.underlying.obj.domain D.underlying.obj.arity)))
      ⟨((rvRightTagMap E.underlying.obj.domain D.underlying.obj.arity).toImage v).val,
        Or.inr ((rvRightTagMap E.underlying.obj.domain D.underlying.obj.arity).toImage v).property⟩).val 0 = _
  rw [Map.union_on_right _ _ (rvTaggedImages_disjoint D.underlying.obj.domain E.underlying.obj.domain)]
  exact congrArg E.form.value (Map.inverse_apply _ _ v)

theorem rvVolumeCoprod_underlying (n : ℕ)
    (U V : RVVolumeObject (M := M) S n) :
    rvVolumeUnderlying S n (rvVolumeCoprod S n U V) =
      rvFiniteCoprodObject (rvVolumeUnderlying S n U) (rvVolumeUnderlying S n V) := by cases n <;> rfl

theorem rvVolumeCoprod_density_left (n : ℕ)
    (U V : RVVolumeObject (M := M) S n) (u : (rvVolumeUnderlying S n U).obj.domain) :
    (rvVolumeForm S n (rvVolumeCoprod S n U V)).value
      ((rvVolumeCoprod_underlying n U V).symm ▸
        rvCoprodLeftMap (rvVolumeUnderlying S n U).obj (rvVolumeUnderlying S n V).obj u) =
      (rvVolumeForm S n U).value u := by
  cases n with
  | zero => rfl
  | succ k => exact coprod_density_left U V u

theorem rvVolumeCoprod_density_right (n : ℕ)
    (U V : RVVolumeObject (M := M) S n) (v : (rvVolumeUnderlying S n V).obj.domain) :
    (rvVolumeForm S n (rvVolumeCoprod S n U V)).value
      ((rvVolumeCoprod_underlying n U V).symm ▸
        rvCoprodRightMap (rvVolumeUnderlying S n U).obj (rvVolumeUnderlying S n V).obj v) =
      (rvVolumeForm S n V).value v := by
  cases n with
  | zero => rfl
  | succ k => exact coprod_density_right U V v

end IntegrationInACVF.Section7
