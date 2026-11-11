import IntegrationSection5.CoordinateCanonicalFibre

/-! A one-coordinate canonical step preserves actual RV-pullbacks. -/
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

theorem coordinateCanonical_preserves_pullback (A : DefSet (M := M) S n m) (i : Fin n)
    (hA : IsRVPullback (carrier A)) : IsRVPullback (carrier (coordinateCanonicalImage A i)) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨a,rfl⟩ q hpq
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp hpq
  let c : Point (M := M) n m := (q.1,a.val.2)
  have hac : SameRV a.val c := (sameRV_iff _ _).mpr ⟨hv,rfl⟩
  let b : A := ⟨c,(isRVPullback_iff _).mp hA _ a.property _ hac⟩
  refine ⟨b,?_⟩
  change coordinateCanonical i c = q
  refine Prod.ext rfl ?_
  funext j
  cases j using Fin.addCases with
  | left j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hh := congrFun hl (Fin.castAdd m 0)
    change rv (vfAt a.val i) = q.2 (Fin.castAdd m 0) at hh
    exact (hv i).symm.trans hh
  | right j =>
    have hh := congrFun hl (Fin.natAdd 1 j)
    change Fin.append (fun _ : Fin 1 => rv (vfAt a.val i)) a.val.2 (Fin.natAdd 1 j) = q.2 (Fin.natAdd 1 j) at hh
    simpa only [coordinateCanonical,c,Fin.append_right] using hh

end IntegrationInACVF.Section5
