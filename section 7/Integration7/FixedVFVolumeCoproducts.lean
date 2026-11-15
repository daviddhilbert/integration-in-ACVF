import Integration7.FixedVFLabelTags
import Integration7.VolumeFormGluing

/-! Positive VF volume coproducts use disjoint RV labels and keep the
VF degree fixed. Each summand retains its literal density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.coprod (U V : PositiveVFVolumeObject (M := M) S k) :
    PositiveVFVolumeObject (M := M) S k where
  arity := 1+(U.arity+V.arity)
  domain := (fixedVFLeftTagMap U.domain V.arity).image.union
    (fixedVFRightTagMap V.domain U.arity).image
  finite_labels x := (fixed_vf_left_tag_finite_labels U.domain V.arity U.finite_labels x).union
    (fixed_vf_right_tag_finite_labels V.domain U.arity V.finite_labels x)
  form := (U.form.pullback (fixedVFUntagLeft U.domain V.arity)).union
    (V.form.pullback (fixedVFUntagRight V.domain U.arity))

def vfVolumeCoprodLeftMap (U V : PositiveVFVolumeObject (M := M) S k) :
    Map U.domain (U.coprod V).domain :=
  (Map.inclusion (show (fixedVFLeftTagMap U.domain V.arity).image.carrier ⊆
    (U.coprod V).domain.carrier from fun _ h => Or.inl h)).comp (fixedVFLeftTagMap U.domain V.arity).toImage

def vfVolumeCoprodRightMap (U V : PositiveVFVolumeObject (M := M) S k) :
    Map V.domain (U.coprod V).domain :=
  (Map.inclusion (show (fixedVFRightTagMap V.domain U.arity).image.carrier ⊆
    (U.coprod V).domain.carrier from fun _ h => Or.inr h)).comp (fixedVFRightTagMap V.domain U.arity).toImage

theorem vf_volume_coprod_cases (U V : PositiveVFVolumeObject (M := M) S k) (p : (U.coprod V).domain) :
    (∃ u : U.domain, vfVolumeCoprodLeftMap U V u = p) ∨
      ∃ v : V.domain, vfVolumeCoprodRightMap U V v = p := by
  rcases p.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · exact Or.inl ⟨u,Subtype.ext hu⟩
  · exact Or.inr ⟨v,Subtype.ext hv⟩

theorem vf_volume_coprod_density_left (U V : PositiveVFVolumeObject (M := M) S k) (u : U.domain) :
    (U.coprod V).form.value (vfVolumeCoprodLeftMap U V u) = U.form.value u := by
  change (((U.form.map.comp (fixedVFUntagLeft U.domain V.arity)).union
    (V.form.map.comp (fixedVFUntagRight V.domain U.arity)))
      ⟨((fixedVFLeftTagMap U.domain V.arity).toImage u).val,
        Or.inl ((fixedVFLeftTagMap U.domain V.arity).toImage u).property⟩).val 0 = _
  rw [Map.union_on_left]
  exact congrArg U.form.value (Map.inverse_apply _ _ u)

theorem vf_volume_coprod_density_right (U V : PositiveVFVolumeObject (M := M) S k) (v : V.domain) :
    (U.coprod V).form.value (vfVolumeCoprodRightMap U V v) = V.form.value v := by
  change (((U.form.map.comp (fixedVFUntagLeft U.domain V.arity)).union
    (V.form.map.comp (fixedVFUntagRight V.domain U.arity)))
      ⟨((fixedVFRightTagMap V.domain U.arity).toImage v).val,
        Or.inr ((fixedVFRightTagMap V.domain U.arity).toImage v).property⟩).val 0 = _
  rw [Map.union_on_right _ _ (fixed_vf_tagged_images_disjoint U.domain V.domain)]
  exact congrArg V.form.value (Map.inverse_apply _ _ v)

end IntegrationInACVF.Section7
