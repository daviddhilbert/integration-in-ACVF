import Section4.RVDimension
import Section4.MapCorestrict
import Section4.VFFibreFiniteness
import Section4.RVCategories

/-! A small exceptional set in the actual volume image pulls back
to a small set of labels because the volume map is finite-to-one. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.VolumeBadLabels

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

noncomputable def labels (U : RVFiniteObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) k) S) :
    DefSet (rawRVSpace (M := M) U.obj.arity) S where
  carrier := {z | ∃ u : U.obj.domain, u.val = z ∧ U.obj.value u ∈ D.carrier}
  definable := U.obj.volume.definable_preimage D.definable

theorem mem_labels (U : RVFiniteObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) k) S) (u : U.obj.domain) :
    u.val ∈ (labels U D).carrier ↔ U.obj.value u ∈ D.carrier := by
  constructor
  · rintro ⟨v,hv,hd⟩
    have he : v = u := Subtype.ext hv
    simpa only [he] using hd
  · exact fun h => ⟨u,rfl,h⟩

theorem dimension_le (U : RVFiniteObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) k) S) : rvDim (labels U D) ≤ rvDim D := by
  have hsub : (labels U D).carrier ⊆ U.obj.domain.carrier := by
    rintro _ ⟨u,rfl,_⟩
    exact u.property
  let g := U.obj.volume.restrict hsub
  let f : Map (labels U D) D := g.corestrict (by
    intro p
    exact (mem_labels U D ⟨p.val,hsub p.property⟩).mp p.property)
  apply rvDim_le_of_finite_map f
  intro d
  have hfin := (U.property.restrict hsub) (⟨d.val,Set.mem_univ _⟩ : DefSet.univ (rawRVSpace (M := M) k) S)
  apply hfin.subset
  intro a ha
  exact Subtype.ext (congrArg (fun y : D => y.val) ha)

end IntegrationInACVF.Section2.VolumeBadLabels
