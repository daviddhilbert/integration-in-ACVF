import IntegrationSection5.RelativeFibreMaps

/-! Restrict an actual focus to one VF-coordinate fibre. Intersecting with
the fibre's RV hull retains the exact focus axioms for arbitrary sources. -/

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

theorem coordinateInsert_replace (i : Fin n) (u : Fin n → VF (M := M))
    (p : Point (M := M) 1 m) (c : VF (M := M)) :
    coordinateInsert i u (replace 0 p c) = replace i (coordinateInsert i u p) c := by
  refine Prod.ext ?_ rfl
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateInsert,replace,vfAt]
  · simp [coordinateInsert,replace,hj]

def fibreFocusLocus (D : Focus A i k) (u : Fin n → VF (M := M)) : Set (Point (M := M) 1 m) :=
  {p | coordinateInsert i u p ∈ D.locus ∧ p ∈ hull (carrier (coordinateFibre A i u))}

theorem fibreFocusLocus_pullback (D : Focus A i k) (u : Fin n → VF (M := M)) :
    IsRVPullback (fibreFocusLocus D u) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨hp,⟨a,ha,hap⟩⟩ q hpq
  exact ⟨(isRVPullback_iff _).mp D.locus_pullback _ hp _ (coordinateInsert_sameRV i u hpq),
    a,ha,hap.trans hpq⟩

def fibreFocusGeometry (D : Focus A i k) (u : Fin n → VF (M := M)) :
    FocusGeometry (carrier (coordinateFibre A i u)) 0 k where
  tagged := by
    intro p hp
    have h := D.tagged (coordinateInsert i u p) hp
    simpa only [coordinateInsert,Function.update_self,vfAt] using h
  locus := fibreFocusLocus D u
  locus_pullback := fibreFocusLocus_pullback D u
  locus_subset := fun _ hp => hp.2
  center := fun p => D.center (coordinateInsert i u p)
  independent := by
    intro p hp q hq he
    have hlabels := congrArg (fun z : Point (M := M) 1 m => z.2) he
    change p.2 = q.2 at hlabels
    have hErase : erase i (coordinateInsert i u p) = erase i (coordinateInsert i u q) := by
      refine Prod.ext ?_ hlabels
      funext j
      by_cases hj : j = i
      · subst j; simp [erase,replace]
      · simp [erase,replace,coordinateInsert,hj]
    exact D.independent _ ⟨hp.1,hp.2.1⟩ _ ⟨hq.1,hq.2.1⟩ hErase
  center_mem := by
    intro p hp
    refine ⟨?_,p,hp.1,?_⟩
    · rw [coordinateInsert_replace]
      exact D.center_mem _ ⟨hp.1,hp.2.1⟩
    · apply (sameRV_iff _ _).mpr
      refine ⟨?_,rfl⟩
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hc := D.center_sameRV (coordinateInsert i u p) ⟨hp.1,hp.2.1⟩
      simpa only [coordinateInsert,replace,Function.update_self,vfAt] using hc.symm

theorem fibreFocusGeometry_eta_insert (D : Focus A i k) (u : Fin n → VF (M := M))
    (p : coordinateFibre A i u) :
    coordinateInsert i u ((fibreFocusGeometry D u).eta p.val) = D.toFocusGeometry.eta (coordinateInsert i u p.val) := by
  by_cases hl : coordinateInsert i u p.val ∈ D.locus
  · have hf : p.val ∈ fibreFocusLocus D u := ⟨hl,subset_hull _ p.property⟩
    change coordinateInsert i u (if p.val ∈ fibreFocusLocus D u then replace 0 p.val (vfAt p.val 0 - D.center (coordinateInsert i u p.val)) else p.val) = _
    rw [if_pos hf,FocusGeometry.eta,if_pos hl,coordinateInsert_replace]
    congr 1
    change vfAt p.val 0 - D.center (coordinateInsert i u p.val) =
      vfAt (coordinateInsert i u p.val) i - D.center (coordinateInsert i u p.val)
    rw [show vfAt (coordinateInsert i u p.val) i = vfAt p.val 0 from Function.update_self _ _ _]
  · have hf : p.val ∉ fibreFocusLocus D u := fun h => hl h.1
    change coordinateInsert i u (if p.val ∈ fibreFocusLocus D u then replace 0 p.val (vfAt p.val 0 - D.center (coordinateInsert i u p.val)) else p.val) = _
    rw [if_neg hf,FocusGeometry.eta,if_neg hl]

end IntegrationInACVF.Section5
