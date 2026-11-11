import IntegrationSection5.VerticalRootFibres
import IntegrationSection5.FibreFocusAssembly

/-! Uniform definability of the vertical mean step, with genuine unary
special foci on every coordinate fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.Milestone0.Transfer
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

def verticalMeanCentre (R : VerticalRootFamily A) (p : Point (M := M) (n+1) m) : VF (M := M) :=
  SpecialTransformations.Section3.Barycentre.mean (R.fibre (dropHead id p))

def verticalMeanEta (R : VerticalRootFamily A) (p : Point (M := M) (n+1) m) : Point (M := M) (n+1) m :=
  if p ∈ R.verticalHull then replace 0 p (vfAt p 0-verticalMeanCentre R p) else p

def verticalMeanActive (R : VerticalRootFamily A) : DefSet (M := M) S (n+1) m :=
  PresentedSet.mk (carrier A ∩ R.verticalHull)
    (SetDefinable.inter _ (setDefinable A) R.verticalHull_definable)

def verticalMeanInactive (R : VerticalRootFamily A) : DefSet (M := M) S (n+1) m :=
  PresentedSet.mk (carrier A \ R.verticalHull)
    (SetDefinable.sdiff _ (setDefinable A) R.verticalHull_definable)

def verticalMeanActiveMap (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) :
    Map (verticalMeanActive R) (PresentedSet.univ (pointSpace (n+1) m) S) :=
  Map.comp (subtractMap 0 (PresentedSet.prod (verticalMeanActive R)
    (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)))
    (Map.pair (Map.id (verticalMeanActive R)) (R.meanMap h00 (d+1) (R.card_bound d hd) (verticalMeanActive R)))

def verticalMeanInactiveMap (R : VerticalRootFamily A) :
    Map (verticalMeanInactive R) (PresentedSet.univ (pointSpace (n+1) m) S) :=
  Map.inclusion (Set.subset_univ _)

theorem verticalMeanActiveMap_apply (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) (p : verticalMeanActive R) :
    (verticalMeanActiveMap R h00 d hd p).val =
      replace 0 p.val (vfAt p.val 0 - verticalMeanCentre R p.val) := rfl

theorem verticalMeanInactiveMap_apply (R : VerticalRootFamily A) (p : verticalMeanInactive R) :
    (verticalMeanInactiveMap R p).val = p.val := rfl

def verticalMeanMap (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) : Map A (PresentedSet.univ (pointSpace (n+1) m) S) :=
  Map.mk (fun p => ⟨verticalMeanEta R p.val,Set.mem_univ _⟩)
    (RelationDefinable.congr _ _
      (RelationDefinable.union _ _ (Map.graph_definable (verticalMeanActiveMap R h00 d hd))
        (Map.graph_definable (verticalMeanInactiveMap R))) (by
      intro p q
      constructor
      · rintro (⟨a,rfl,he⟩ | ⟨a,rfl,he⟩)
        · refine ⟨⟨a.val,a.property.1⟩,rfl,?_⟩
          have he' := (verticalMeanActiveMap_apply R h00 d hd a).symm.trans he
          simpa only [verticalMeanEta,if_pos a.property.2] using he'
        · refine ⟨⟨a.val,a.property.1⟩,rfl,?_⟩
          have he' := (verticalMeanInactiveMap_apply R a).symm.trans he
          simpa only [verticalMeanEta,if_neg a.property.2] using he'
      · rintro ⟨a,rfl,he⟩
        by_cases hl : a.val ∈ R.verticalHull
        · refine Or.inl ⟨⟨a.val,a.property,hl⟩,rfl,?_⟩
          exact (verticalMeanActiveMap_apply R h00 d hd ⟨a.val,a.property,hl⟩).trans (by
            simpa only [verticalMeanEta,if_pos hl] using he)
        · refine Or.inr ⟨⟨a.val,a.property,hl⟩,rfl,?_⟩
          exact (verticalMeanInactiveMap_apply R ⟨a.val,a.property,hl⟩).trans (by
            simpa only [verticalMeanEta,if_neg hl] using he)))

theorem verticalMeanMap_unaryRelative (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) : UnaryRelative (Map.toImage (verticalMeanMap R h00 d hd)) 0 := by
  intro a j hj
  change vfAt (verticalMeanEta R a.val) j = vfAt a.val j
  by_cases h : a.val ∈ R.verticalHull <;> simp [verticalMeanEta,h,replace,hj,vfAt]

theorem dropHead_coordinateInsert (u : Fin (n+1) → VF (M := M)) (p : Point (M := M) 1 m) :
    dropHead id (coordinateInsert 0 u p) = verticalTail u p.2 := by
  refine Prod.ext ?_ rfl
  funext j
  simp [dropHead,coordinateInsert,verticalTail,Fin.succ_ne_zero]

def verticalMeanFibreFocus (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k)
    (u : Fin (n+1) → VF (M := M)) : Focus (coordinateFibre A 0 u) 0 k :=
  (verticalRootFibre R u).focus h00 d (verticalRootFibre_bound R u d hd) (coordinateFibre_tagged 0 u hTag)

theorem coordinateInsert_verticalMeanEta (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k)
    (u : Fin (n+1) → VF (M := M)) (p : Point (M := M) 1 m) :
    coordinateInsert 0 u ((verticalMeanFibreFocus R h00 d hd hTag u).toFocusGeometry.eta p) =
      verticalMeanEta R (coordinateInsert 0 u p) := by
  have hmean : SpecialTransformations.Section3.Barycentre.mean ((verticalRootFibre R u).fibre p.2) =
      verticalMeanCentre R (coordinateInsert 0 u p) := by
    rw [verticalRootFibre_fibre]
    unfold verticalMeanCentre
    rw [dropHead_coordinateInsert]
  change coordinateInsert 0 u (if p ∈ hull (carrier (verticalRootFibre R u).set) then
    replace 0 p (vfAt p 0-SpecialTransformations.Section3.Barycentre.mean ((verticalRootFibre R u).fibre p.2)) else p) = _
  by_cases hl : coordinateInsert 0 u p ∈ R.verticalHull
  · have hf := (verticalRootFibre_hull R u p).mpr hl
    rw [if_pos hf,coordinateInsert_replace,hmean]
    rw [verticalMeanEta,if_pos hl]
    simp only [coordinateInsert,vfAt,Function.update_self]
  · have hf : p ∉ hull (carrier (verticalRootFibre R u).set) := fun h => hl ((verticalRootFibre_hull R u p).mp h)
    rw [if_neg hf]
    exact (if_neg hl).symm

theorem verticalMeanMap_specialRelative (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) (hd : R.Bound d) {k : Fin m} (hTag : Tagged (carrier A) 0 k) :
    SpecialRelative (Map.toImage (verticalMeanMap R h00 d hd)) 0 := by
  apply specialRelative_of_fibre_focus (verticalMeanMap R h00 d hd)
    (verticalMeanMap_unaryRelative R h00 d hd) (verticalMeanFibreFocus R h00 d hd hTag)
  intro u p
  exact coordinateInsert_verticalMeanEta R h00 d hd hTag u p.val

end IntegrationInACVF.Section5
