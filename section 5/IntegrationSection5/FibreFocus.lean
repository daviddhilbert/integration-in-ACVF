import IntegrationSection5.FibreFocusGeometry

/-! Definability of an actual coordinate-fibre focus over the base obtained
by naming precisely the other VF coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

theorem fibreFocusLocus_definable (D : Focus A i k) (u : Fin n → VF (M := M)) :
    SetDefinable (pointSpace 1 m) (coordinateFibreBase S i u) (fibreFocusLocus D u) := by
  let L : DefSet (M := M) S n m := PresentedSet.mk D.locus D.locus_definable
  exact SetDefinable.inter _ (setDefinable (coordinateFibre L i u))
    (hull_definable (coordinateFibre A i u))

def fibreFocusActive (D : Focus A i k) (u : Fin n → VF (M := M)) :
    DefSet (M := M) (coordinateFibreBase S i u) 1 m :=
  PresentedSet.mk (carrier (coordinateFibre A i u) ∩ fibreFocusLocus D u)
    (SetDefinable.inter _ (setDefinable (coordinateFibre A i u)) (fibreFocusLocus_definable D u))

def fibreFocusActiveEmbedding (D : Focus A i k) (u : Fin n → VF (M := M)) :
    Map (fibreFocusActive D u)
      (extendBase D.active (Set.subset_union_left : S ⊆ coordinateFibreBase S i u)) :=
  let g := Map.comp (coordinateInsertMap S i u)
    (Map.inclusion (Set.subset_univ _) : Map (fibreFocusActive D u)
      (PresentedSet.univ (pointSpace 1 m) (coordinateFibreBase S i u)))
  mapIntoSubset g _ (fun a => ⟨a.property.1,a.property.2.1⟩)

def fibreFocusCentreMap (D : Focus A i k) (u : Fin n → VF (M := M)) :
    Map (fibreFocusActive D u)
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (coordinateFibreBase S i u)) :=
  Map.comp (@SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (@CanonicalStructure.normalize M sM) (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1)
    S (coordinateFibreBase S i u) D.active (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)
    D.centerMap Set.subset_union_left)
    (fibreFocusActiveEmbedding D u)

theorem fibreFocusCentre_graph (D : Focus A i k) (u : Fin n → VF (M := M)) :
    RelationDefinable (pointSpace 1 m) (SpecialTransformations.Section4.vfSpace 1)
      (coordinateFibreBase S i u)
      (fun p z => p ∈ carrier (coordinateFibre A i u) ∩ fibreFocusLocus D u ∧
        z 0 = D.center (coordinateInsert i u p)) := by
  apply RelationDefinable.congr _ _ (Map.graph_definable (fibreFocusCentreMap D u))
  intro p z
  constructor
  · rintro ⟨a,rfl,hz⟩
    refine ⟨a.property,?_⟩
    exact (congrFun hz 0).symm
  · rintro ⟨hp,hz⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hz.symm

def fibreFocus (D : Focus A i k) (u : Fin n → VF (M := M)) :
    Focus (coordinateFibre A i u) 0 k where
  toFocusGeometry := fibreFocusGeometry D u
  locus_definable := fibreFocusLocus_definable D u
  center_graph := fibreFocusCentre_graph D u

end IntegrationInACVF.Section5
