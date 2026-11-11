import IntegrationSection5.CoordinateCanonicalFibre
import Section5.Assembly

/-! A saturated coordinate fibre gives exactly the natural one-coordinate
lift of its contracted image. -/
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
variable {S : Set M} {n m : ℕ}

theorem coordinateCanonical_headKey (p : Point (M := M) (n+1) m) :
    dropHead id (coordinateCanonical 0 p) = headKey p := rfl

theorem headSaturated_iff_coordinateFibre (A : DefSet (M := M) S (n+1) m) :
    HeadSaturated (carrier A) ↔ ∀ u, IsRVPullback (carrier (coordinateFibre A 0 u)) := by
  constructor
  · intro h u
    apply (isRVPullback_iff _).mpr
    intro p hp q hpq
    have hx := ((sameRV_iff _ _).mp hpq).1 0
    have h := h (coordinateInsert 0 u p) hp (vfAt q 0)
      (by simpa only [coordinateInsert,vfAt,Function.update_self] using hx.symm)
    have he : replace 0 (coordinateInsert 0 u p) (vfAt q 0) = coordinateInsert 0 u q := by
      refine Prod.ext ?_ ((sameRV_iff _ _).mp hpq).2
      funext j
      by_cases hj : j = 0
      · subst j; simp [replace,coordinateInsert,vfAt]
      · simp [replace,coordinateInsert,hj]
    change coordinateInsert 0 u q ∈ carrier A
    rw [← he]
    exact h
  · intro h p hp x hx
    let u := p.1
    have hRestore : coordinateInsert 0 u (coordinateProject 0 p) = p :=
      coordinateInsert_project 0 u p (fun _ _ => rfl)
    have hp' : coordinateProject 0 p ∈ carrier (coordinateFibre A 0 u) := by
      change coordinateInsert 0 u (coordinateProject 0 p) ∈ carrier A
      rw [hRestore]
      exact hp
    have he : SameRV (coordinateProject 0 p) (replace 0 (coordinateProject 0 p) x) :=
      sameRV_replace 0 (coordinateProject 0 p) x hx
    have hh := (isRVPullback_iff _).mp (h u) _ hp' _ he
    change coordinateInsert 0 u (replace 0 (coordinateProject 0 p) x) ∈ carrier A at hh
    rwa [coordinateInsert_replace,hRestore] at hh

theorem coordinateCanonical_image_headLift (A : DefSet (M := M) S (n+1) m)
    (hA : HeadSaturated (carrier A)) (q : Point (M := M) (n+1) (1+m)) :
    q ∈ carrier (coordinateCanonicalImage A 0) ↔
      dropHead id q ∈ carrier (headImage A) ∧ q.2 (Fin.castAdd m 0) = rv (vfAt q 0) := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a,headKeyMap_apply A a⟩,rfl⟩
  · rintro ⟨⟨a,ha⟩,hTag⟩
    have ha' : headKey a.val = dropHead id q := (headKeyMap_apply A a).symm.trans ha
    have hHeadRV : rv (vfAt q 0) = rv (vfAt a.val 0) := by
      have he := congrArg (fun p : Point (M := M) n (1+m) => p.2 (Fin.castAdd m 0)) ha'
      exact hTag.symm.trans he.symm
    let p : A := ⟨replace 0 a.val (vfAt q 0),hA a.val a.property _ hHeadRV⟩
    refine ⟨p,?_⟩
    change coordinateCanonical 0 p.val = q
    refine Prod.ext ?_ ?_
    · funext j
      cases j using Fin.cases with
      | zero => simp [p,coordinateCanonical,replace,vfAt]
      | succ j =>
        have h := congrArg (fun z : Point (M := M) n (1+m) => vfAt z j) ha'
        simpa only [coordinateCanonical,p,replace,Function.update_of_ne (Fin.succ_ne_zero j),headKey,dropHead,vfAt] using h
    · funext j
      cases j using Fin.addCases with
      | left j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simpa only [coordinateCanonical,Fin.append_left,p,replace,Function.update_self,vfAt] using hTag.symm
      | right j =>
        have h := congrArg (fun z : Point (M := M) n (1+m) => z.2 (Fin.natAdd 1 j)) ha'
        simpa only [coordinateCanonical,Fin.append_right,p,replace,headKey,dropHead,id_eq] using h

end IntegrationInACVF.Section5
