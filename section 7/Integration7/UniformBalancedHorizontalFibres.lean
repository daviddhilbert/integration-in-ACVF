import Integration7.UniformBalancedHorizontalCentreValues
import IntegrationSection4.BalancedBallClasses

/-! Exact horizontal fibres of the entire balanced-row graph family.
All original and refinement RV labels remain frozen in this identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

set_option maxHeartbeats 1000000 in
theorem horizontal_graph_fibre (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : A) (x : VF (M := M)) :
    replace 1 (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val x ∈
      carrier (gammaRVGraphRefinement A F.parameters hNames) ↔
    (x,vfAt a.val 0) ∈ mixedPairFibre F.parameters a := by
  constructor
  · rintro ⟨b,hb⟩
    have hVF := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.1) hb
    have hP : F.parameters.toFun b = F.parameters.toFun a := by
      funext i
      have ht := congrArg (fun p : Point (M := M) 2 (m+F.arity) => p.2 (Fin.natAdd m i)) hb
      change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
        Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at ht
      simpa only [Fin.append_right] using ht
    refine ⟨b,?_,hP⟩
    refine hVF.trans ?_
    funext i
    fin_cases i <;> rfl
  · rintro ⟨b,hVF,hP⟩
    have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hP)).2
    refine ⟨b,?_⟩
    change (b.val.1,Fin.append b.val.2 (F.parameters.toFun b)) =
      replace 1 (a.val.1,Fin.append a.val.2 (F.parameters.toFun a)) x
    apply Prod.ext
    · refine hVF.trans ?_
      funext i
      fin_cases i <;> rfl
    · exact congrArg₂ Fin.append hOld hP

set_option maxHeartbeats 1200000 in
theorem source_horizontal_fibre (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S)
    (q : gammaRVGraphRefinement A F.parameters hNames) :
    ∃ r : RV (M := M),
      {x : VF (M := M) | replace 1 q.val x ∈ carrier (gammaRVGraphRefinement A F.parameters hNames)} =
        BalancedFibres.translatedRV r ((F.horizontalCentreMap hBalanced hNames q).val 0) := by
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  obtain ⟨r,hBal⟩ := hBalanced a
  obtain ⟨b,hP,hCentre⟩ := F.balanced_centre_covers_head hBalanced a
  have hCb := F.horizontal_centre_on_graph hBalanced hNames a b hP hCentre
  have hbR : (vfAt b.val 1,vfAt b.val 0) ∈ mixedPairFibre F.parameters a := by
    refine ⟨b,?_,hP⟩
    funext i
    fin_cases i <;> rfl
  have hbD : vfAt b.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := ⟨_,hbR,rfl⟩
  have hPosition : F.localPosition a (vfAt b.val 1) = vfAt a.val 0 :=
    (F.centre_eq_local_position a b hP).symm.trans hCentre
  refine ⟨r,?_⟩
  ext x
  refine (F.horizontal_graph_fibre hNames a x).trans ?_
  change (x,vfAt a.val 0) ∈ mixedPairFibre F.parameters a ↔
    rv (x-(show VF (M := M) from (F.horizontalCentreMap hBalanced hNames
      (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).val 0)) = r
  rw [hCb]
  constructor
  · intro hx
    have hxD : x ∈ Cells.first (mixedPairFibre F.parameters a) := ⟨_,hx,rfl⟩
    apply (Set.ext_iff.mp (hBal.2.2.1.horizontal x hxD) (vfAt b.val 1)).mp
    exact ⟨hbD,by change (x,F.localPosition a (vfAt b.val 1)) ∈ mixedPairFibre F.parameters a; rwa [hPosition]⟩
  · intro hx
    have hxD := BalancedBallClasses.positive_class_subset hBal.2.2.1 hBal.1 (vfAt b.val 1) hbD hx
    have hh := ((Set.ext_iff.mp (hBal.2.2.1.horizontal x hxD) (vfAt b.val 1)).mpr hx).2
    change (x,F.localPosition a (vfAt b.val 1)) ∈ mixedPairFibre F.parameters a at hh
    simpa only [hPosition] using hh

end IntegrationInACVF.Section7.UniformMixedCellPresentation
