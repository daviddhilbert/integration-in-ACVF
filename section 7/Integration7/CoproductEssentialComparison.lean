import Integration7.EssentialVolumeCoproduct
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def coprodEssentialMergeMap (U V : PositiveRVVolumeObject (M := M) S k) :
    Map (rvFiniteCoprodObject U.essential V.essential).obj.domain (U.coprod V).essential.obj.domain :=
  ((coprodEssentialLeftMap U V).comp (rvUntagLeft U.essential.obj.domain V.essential.obj.arity)).union
    ((coprodEssentialRightMap U V).comp (rvUntagRight V.essential.obj.domain U.essential.obj.arity))

theorem coprodEssentialMergeMap_left (U V : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) :
    coprodEssentialMergeMap U V (rvCoprodLeftMap U.essential.obj V.essential.obj u) =
      coprodEssentialLeftMap U V u := by
  change (((coprodEssentialLeftMap U V).comp (rvUntagLeft U.essential.obj.domain V.essential.obj.arity)).union
    ((coprodEssentialRightMap U V).comp (rvUntagRight V.essential.obj.domain U.essential.obj.arity)))
    ⟨((rvLeftTagMap U.essential.obj.domain V.essential.obj.arity).toImage u).val,
      Or.inl ((rvLeftTagMap U.essential.obj.domain V.essential.obj.arity).toImage u).property⟩ = _
  rw [Map.union_on_left]
  exact congrArg (coprodEssentialLeftMap U V) (Map.inverse_apply _ _ u)

theorem coprodEssentialMergeMap_right (U V : PositiveRVVolumeObject (M := M) S k)
    (v : V.essential.obj.domain) :
    coprodEssentialMergeMap U V (rvCoprodRightMap U.essential.obj V.essential.obj v) =
      coprodEssentialRightMap U V v := by
  change (((coprodEssentialLeftMap U V).comp (rvUntagLeft U.essential.obj.domain V.essential.obj.arity)).union
    ((coprodEssentialRightMap U V).comp (rvUntagRight V.essential.obj.domain U.essential.obj.arity)))
    ⟨((rvRightTagMap V.essential.obj.domain U.essential.obj.arity).toImage v).val,
      Or.inr ((rvRightTagMap V.essential.obj.domain U.essential.obj.arity).toImage v).property⟩ = _
  rw [Map.union_on_right _ _ (rvTaggedImages_disjoint U.essential.obj.domain V.essential.obj.domain)]
  exact congrArg (coprodEssentialRightMap U V) (Map.inverse_apply _ _ v)

theorem coprodEssentialMergeMap_value (U V : PositiveRVVolumeObject (M := M) S k)
    (p : (rvFiniteCoprodObject U.essential V.essential).obj.domain) :
    (coprodEssentialMergeMap U V p).val = p.val := by
  rcases p.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have he : rvCoprodLeftMap U.essential.obj V.essential.obj u = p := Subtype.ext hu
    rw [← he, coprodEssentialMergeMap_left]
    rfl
  · have he : rvCoprodRightMap U.essential.obj V.essential.obj v = p := Subtype.ext hv
    rw [← he, coprodEssentialMergeMap_right]
    rfl

theorem coprodEssentialMergeMap_coordinates (U V : PositiveRVVolumeObject (M := M) S k)
    (p : (rvFiniteCoprodObject U.essential V.essential).obj.domain) :
    (U.coprod V).essential.obj.value (coprodEssentialMergeMap U V p) =
      (rvFiniteCoprodObject U.essential V.essential).obj.value p := by
  rcases p.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have he : rvCoprodLeftMap U.essential.obj V.essential.obj u = p := Subtype.ext hu
    rw [← he, coprodEssentialMergeMap_left, coprodEssentialLeftMap_coordinates]
    exact (rvCoprod_value_left U.essential.obj V.essential.obj u).symm
  · have he : rvCoprodRightMap U.essential.obj V.essential.obj v = p := Subtype.ext hv
    rw [← he, coprodEssentialMergeMap_right, coprodEssentialRightMap_coordinates]
    exact (rvCoprod_value_right U.essential.obj V.essential.obj v).symm

theorem coprodEssentialMergeMap_bijective (U V : PositiveRVVolumeObject (M := M) S k) :
    Function.Bijective (coprodEssentialMergeMap U V) := by
  constructor
  · intro a b he
    apply Subtype.ext
    have h := congrArg (fun z : (U.coprod V).essential.obj.domain => z.val) he
    simpa only [coprodEssentialMergeMap_value] using h
  · intro w
    rcases coprodEssential_cover U V w with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact ⟨rvCoprodLeftMap U.essential.obj V.essential.obj u, (coprodEssentialMergeMap_left U V u).trans hu⟩
    · exact ⟨rvCoprodRightMap U.essential.obj V.essential.obj v, (coprodEssentialMergeMap_right U V v).trans hv⟩

def coprodEssentialComparisonIso (U V : PositiveRVVolumeObject (M := M) S k) :
    rvFiniteCoprodObject U.essential V.essential ≅ (U.coprod V).essential :=
  rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (coprodEssentialMergeMap U V)
    (coprodEssentialMergeMap_bijective U V) (coprodEssentialMergeMap_coordinates U V))

theorem coprodEssentialComparisonIso_left (U V : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) :
    finiteIsoMap (coprodEssentialComparisonIso U V) (rvCoprodLeftMap U.essential.obj V.essential.obj u) =
      coprodEssentialLeftMap U V u := coprodEssentialMergeMap_left U V u

theorem coprodEssentialComparisonIso_right (U V : PositiveRVVolumeObject (M := M) S k)
    (v : V.essential.obj.domain) :
    finiteIsoMap (coprodEssentialComparisonIso U V) (rvCoprodRightMap U.essential.obj V.essential.obj v) =
      coprodEssentialRightMap U V v := coprodEssentialMergeMap_right U V v
end IntegrationInACVF.Section7
