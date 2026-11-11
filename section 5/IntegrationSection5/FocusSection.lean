import Section5.Core

/-! The definable section of a focus: replace the active coordinate by its
focus, retaining all labels. On an RV-pullback its value lies in the original
set. This will pull target focus points back along the given bijection. -/

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

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def replaceCoordinateMap (j : Fin n)
    (A : PresentedSet (spaceProd (pointSpace (M := M) n m)
      (SpecialTransformations.Section4.vfSpace 1)) S) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (fun p => replace j p.1 (p.2 0))
    (fun z => Sum.elim
      (fun i => if i = j then z (.inr 0) else z (.inl (.inl i)))
      (fun i => z (.inl (.inr i))))
    (by
      intro i
      cases i with
      | inl i =>
        by_cases hi : i = j
        · simpa [hi] using rawProj S (.inr 0 : (Fin n ⊕ Fin m) ⊕ Fin 1)
        · simpa [hi] using rawProj S (.inl (.inl i) : (Fin n ⊕ Fin m) ⊕ Fin 1)
      | inr i => exact rawProj S (.inl (.inr i) : (Fin n ⊕ Fin m) ⊕ Fin 1))
    (by
      intro c
      refine ⟨?_, c.property.1.2⟩
      intro i
      by_cases hi : i = j
      · simpa [hi, Function.comp_def] using c.property.2 0
      · simpa [hi, Function.comp_def] using c.property.1.1 i)
    (by
      intro c
      refine Prod.ext ?_ rfl
      funext i
      by_cases hi : i = j
      · subst i
        apply Subtype.ext
        simp [replace]
      · apply Subtype.ext
        simp [replace, hi])

def activeFocusSection {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) : Map D.active (PresentedSet.univ (pointSpace n m) S) :=
  Map.comp (replaceCoordinateMap j
    (PresentedSet.prod D.active (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S)))
    (Map.pair (Map.id D.active) D.centerMap)

@[simp] theorem activeFocusSection_apply
    {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (a : D.active) :
    (activeFocusSection D a).val = replace j a.val (D.center a.val) := rfl

def focusSectionFun {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : IsRVPullback (carrier A)) (a : A) : A :=
  if h : a.val ∈ D.locus then
    ⟨replace j a.val (D.center a.val),
      (Set.ext_iff.mp hA _).mp (D.locus_subset (D.center_mem a.val ⟨a.property, h⟩))⟩
  else a

def focusSectionMap {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : IsRVPullback (carrier A)) : Map A A :=
  Map.mk (focusSectionFun D hA) (by
    apply RelationDefinable.congr _ _
      (RelationDefinable.union _ _ (Map.graph_definable (activeFocusSection D))
        (Map.graph_definable D.inactiveMap))
    intro p q
    constructor
    · rintro (⟨a, rfl, he⟩ | ⟨a, rfl, he⟩)
      · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
        rw [activeFocusSection_apply] at he
        simpa only [focusSectionFun, dite_eq_left a.property.2] using he
      · refine ⟨⟨a.val, a.property.1⟩, rfl, ?_⟩
        rw [Focus.inactiveMap_apply] at he
        simpa only [focusSectionFun, dite_eq_right a.property.2] using he
    · rintro ⟨a, rfl, he⟩
      by_cases ha : a.val ∈ D.locus
      · left
        refine ⟨⟨a.val, a.property, ha⟩, rfl, ?_⟩
        rw [activeFocusSection_apply]
        simpa only [focusSectionFun, dite_eq_left ha] using he
      · right
        refine ⟨⟨a.val, a.property, ha⟩, rfl, ?_⟩
        rw [Focus.inactiveMap_apply]
        simpa only [focusSectionFun, dite_eq_right ha] using he)

theorem focusSectionMap_active {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : IsRVPullback (carrier A)) (a : A) (ha : a.val ∈ D.locus) :
    (focusSectionMap D hA a).val = replace j a.val (D.center a.val) := by
  simp only [focusSectionMap, focusSectionFun, dite_eq_left ha]

theorem focusSectionMap_inactive {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : IsRVPullback (carrier A)) (a : A) (ha : a.val ∉ D.locus) :
    focusSectionMap D hA a = a := by
  simp only [focusSectionMap, focusSectionFun, dite_eq_right ha]

theorem focusSectionMap_sameRV {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : Focus A j k) (hA : IsRVPullback (carrier A)) (a : A) :
    SameRV (focusSectionMap D hA a).val a.val := by
  by_cases ha : a.val ∈ D.locus
  · rw [focusSectionMap_active D hA a ha]
    apply (sameRV_iff _ _).mpr
    refine ⟨?_, rfl⟩
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [replace, Function.update_self] using D.center_sameRV a.val ⟨a.property, ha⟩
    · simp [replace, hi]
  · rw [focusSectionMap_inactive D hA a ha]
    rfl

theorem unary_focusSectionMap_eq {A : DefSet (M := M) S 1 m} {k : Fin m}
    (D : Focus A 0 k) (hA : IsRVPullback (carrier A)) (a b : A)
    (ha : a.val ∈ D.locus) (he : SameRV a.val b.val) :
    focusSectionMap D hA a = focusSectionMap D hA b := by
  have hb := (mem_iff_sameRV D.locus_pullback he).mp ha
  have herase : erase 0 a.val = erase 0 b.val := by
    refine Prod.ext ?_ ((sameRV_iff _ _).mp he).2
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [erase, replace]
  have hc := D.independent a.val ⟨a.property, ha⟩ b.val ⟨b.property, hb⟩ herase
  apply Subtype.ext
  rw [focusSectionMap_active D hA a ha, focusSectionMap_active D hA b hb]
  refine Prod.ext ?_ ((sameRV_iff _ _).mp he).2
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [replace, Function.update_self] using hc

end IntegrationInACVF.Section5
