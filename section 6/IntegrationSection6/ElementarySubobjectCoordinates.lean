import IntegrationSection6.ElementaryRestrictions
import IntegrationSection6.ElementaryCoordinates

/-! Elementary blowup restrictions keep literal tuple labels and partition
the actual elementary domain into two disjoint images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
variable (U : RVObject (M := M) S n) (i : Fin n)
variable (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)

theorem elementarySubobjectMap_labels (a : (elementary (U.restrict A hA) i).domain) :
    (elementarySubobjectMap U i A hA a).val = a.val := by
  rw [elementarySubobjectMap,elementaryMap_labels,← elementaryParameter_labels]
  exact (elementary_labels (U.restrict A hA) i a).symm

theorem elementarySubobjectMap_volume (a : (elementary (U.restrict A hA) i).domain) :
    (elementary U i).value (elementarySubobjectMap U i A hA a) = (elementary (U.restrict A hA) i).value a := by
  rw [elementary_value,elementarySubobjectMap,elementaryMap_projection,elementaryMap_parameter,elementary_value]
  rfl

theorem elementarySubobjects_disjoint :
    Disjoint (elementarySubobject U i A hA).carrier
      (elementarySubobject U i (complement U A) (complement_subset U A)).carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  let a : (elementary U i).domain := ⟨x,elementarySubobject_subset U i A hA hx⟩
  have hp := (mem_elementarySubobject U i A hA a).mp hx
  exact ((mem_elementarySubobject U i (complement U A) (complement_subset U A) a).mp hy).2 hp

theorem elementarySubobjects_cover :
    (elementarySubobject U i A hA).carrier ∪
      (elementarySubobject U i (complement U A) (complement_subset U A)).carrier = (elementary U i).domain.carrier := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact elementarySubobject_subset U i A hA hx
    · exact elementarySubobject_subset U i (complement U A) (complement_subset U A) hx
  · intro hx
    let a : (elementary U i).domain := ⟨x,hx⟩
    by_cases ha : (elementaryProjection U i a).val ∈ A.carrier
    · exact Or.inl ((mem_elementarySubobject U i A hA a).mpr ha)
    · exact Or.inr ((mem_elementarySubobject U i (complement U A) (complement_subset U A) a).mpr
        ⟨(elementaryProjection U i a).property,ha⟩)

end IntegrationInACVF.Section6
