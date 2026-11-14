import Integration7.ExplicitRVCoproductAssociativity
import Integration7.VolumeCoproduct
import Integration7.VolumeRelabeling

/-! The structural coproduct bijections preserve coordinates and densities. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volumeCoprod_cases (U V : PositiveRVVolumeObject (M := M) S k)
    (w : (U.coprod V).underlying.obj.domain) :
    (∃ u, rvCoprodLeftMap U.underlying.obj V.underlying.obj u = w) ∨
      (∃ v, rvCoprodRightMap U.underlying.obj V.underlying.obj v = w) := by
  rcases w.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨u, Subtype.ext hu⟩
  · exact Or.inr ⟨v, Subtype.ext hv⟩

def volumeCoprodSwap (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.coprod V) (V.coprod U) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvCoprodSwapExplicit U.underlying.obj V.underlying.obj))
  · intro w
    rcases volumeCoprod_cases U V w with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · change (rvCoprodObject V.underlying.obj U.underlying.obj).value
        ((rvCoprodSwapExplicit U.underlying.obj V.underlying.obj).hom.map
          (rvCoprodLeftMap U.underlying.obj V.underlying.obj u)) =
        (rvCoprodObject U.underlying.obj V.underlying.obj).value
          (rvCoprodLeftMap U.underlying.obj V.underlying.obj u)
      rw [rvCoprodSwapExplicit_left, rvCoprod_value_right, rvCoprod_value_left]
    · change (rvCoprodObject V.underlying.obj U.underlying.obj).value
        ((rvCoprodSwapExplicit U.underlying.obj V.underlying.obj).hom.map
          (rvCoprodRightMap U.underlying.obj V.underlying.obj v)) =
        (rvCoprodObject U.underlying.obj V.underlying.obj).value
          (rvCoprodRightMap U.underlying.obj V.underlying.obj v)
      rw [rvCoprodSwapExplicit_right, rvCoprod_value_left, rvCoprod_value_right]
  · intro w
    rcases volumeCoprod_cases U V w with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · change (V.coprod U).form.value
        ((rvCoprodSwapExplicit U.underlying.obj V.underlying.obj).hom.map
          (rvCoprodLeftMap U.underlying.obj V.underlying.obj u)) = _
      rw [rvCoprodSwapExplicit_left, coprod_density_right, coprod_density_left]
    · change (V.coprod U).form.value
        ((rvCoprodSwapExplicit U.underlying.obj V.underlying.obj).hom.map
          (rvCoprodRightMap U.underlying.obj V.underlying.obj v)) = _
      rw [rvCoprodSwapExplicit_right, coprod_density_left, coprod_density_right]

def volumeCoprodAssoc (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso ((U.coprod V).coprod W) (U.coprod (V.coprod W)) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj))
  · intro z
    rcases volumeCoprod_cases (U.coprod V) W z with ⟨a, rfl⟩ | ⟨w, rfl⟩
    · rcases volumeCoprod_cases U V a with ⟨u, rfl⟩ | ⟨v, rfl⟩
      · change (rvCoprodObject U.underlying.obj (rvCoprodObject V.underlying.obj W.underlying.obj)).value
          ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodLeftMap U.underlying.obj V.underlying.obj u))) =
          (rvCoprodObject (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj).value
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodLeftMap U.underlying.obj V.underlying.obj u))
        rw [rvCoprodAssocExplicit_left, rvCoprod_value_left, rvCoprod_value_left, rvCoprod_value_left]
      · change (rvCoprodObject U.underlying.obj (rvCoprodObject V.underlying.obj W.underlying.obj)).value
          ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodRightMap U.underlying.obj V.underlying.obj v))) =
          (rvCoprodObject (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj).value
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodRightMap U.underlying.obj V.underlying.obj v))
        rw [rvCoprodAssocExplicit_middle, rvCoprod_value_right, rvCoprod_value_left,
          rvCoprod_value_left, rvCoprod_value_right]
    · change (rvCoprodObject U.underlying.obj (rvCoprodObject V.underlying.obj W.underlying.obj)).value
        ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
          (rvCoprodRightMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj w)) =
        (rvCoprodObject (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj).value
          (rvCoprodRightMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj w)
      rw [rvCoprodAssocExplicit_right, rvCoprod_value_right, rvCoprod_value_right, rvCoprod_value_right]
  · intro z
    rcases volumeCoprod_cases (U.coprod V) W z with ⟨a, rfl⟩ | ⟨w, rfl⟩
    · rcases volumeCoprod_cases U V a with ⟨u, rfl⟩ | ⟨v, rfl⟩
      · change (U.coprod (V.coprod W)).form.value
          ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodLeftMap U.underlying.obj V.underlying.obj u))) = _
        rw [rvCoprodAssocExplicit_left]
        exact (coprod_density_left U (V.coprod W) u).trans
          (((coprod_density_left (U.coprod V) W
            (rvCoprodLeftMap U.underlying.obj V.underlying.obj u)).trans
            (coprod_density_left U V u)).symm)
      · change (U.coprod (V.coprod W)).form.value
          ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
            (rvCoprodLeftMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj
              (rvCoprodRightMap U.underlying.obj V.underlying.obj v))) = _
        rw [rvCoprodAssocExplicit_middle]
        exact ((coprod_density_right U (V.coprod W)
          (rvCoprodLeftMap V.underlying.obj W.underlying.obj v)).trans
          (coprod_density_left V W v)).trans
          (((coprod_density_left (U.coprod V) W
            (rvCoprodRightMap U.underlying.obj V.underlying.obj v)).trans
            (coprod_density_right U V v)).symm)
    · change (U.coprod (V.coprod W)).form.value
        ((rvCoprodAssocExplicit U.underlying.obj V.underlying.obj W.underlying.obj).hom.map
          (rvCoprodRightMap (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj w)) = _
      rw [rvCoprodAssocExplicit_right]
      exact ((coprod_density_right U (V.coprod W)
        (rvCoprodRightMap V.underlying.obj W.underlying.obj w)).trans
        (coprod_density_right V W w)).trans
        (coprod_density_right (U.coprod V) W w).symm

end IntegrationInACVF.Section7
