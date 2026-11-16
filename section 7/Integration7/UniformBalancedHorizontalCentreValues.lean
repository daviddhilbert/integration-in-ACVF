module

public import Integration7.UniformBalancedHorizontalCentres

@[expose] public section

/-! Evaluation of the actual horizontal inverse centre on the graph
refinement, using the global mixed positioning bijection. -/
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
theorem horizontal_centre_on_graph (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S)
    (a b : A) (hP : F.parameters.toFun b = F.parameters.toFun a)
    (hCentre : F.centre b = vfAt a.val 0) :
    (F.horizontalCentreMap hBalanced hNames
      (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).val 0 = vfAt b.val 1 := by
  let H := gammaRVGraphRefinement A F.parameters hNames
  let f := Map.toImage (F.positionMap hNames)
  let hf := F.position_to_image_bijective hBalanced hNames
  let k := VerticalOffsets.toKey H (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b)
  have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hP)).2
  have hInput : F.headToPositionImage hBalanced hNames
      (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a) = f k := by
    apply Subtype.ext
    refine Eq.trans ?_ (F.position_map_on_graph hNames b).symm
    change (fun _ : Fin 1 => vfAt a.val 0,Fin.append a.val.2 (F.parameters.toFun a)) =
      (fun _ : Fin 1 => F.centre b,Fin.append b.val.2 (F.parameters.toFun b))
    apply Prod.ext
    · funext i
      exact hCentre.symm
    · exact congrArg₂ Fin.append hOld.symm hP.symm
  have hInv := congrArg (Map.inverse f hf) hInput
  rw [Map.inverse_apply] at hInv
  exact congrArg (fun z : VerticalOffsets.keyImage H => vfAt z.val 0) hInv

end IntegrationInACVF.Section7.UniformMixedCellPresentation
