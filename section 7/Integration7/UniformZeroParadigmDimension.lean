module

public import Integration7.UniformCellHeadFibres
public import Integration7.MixedCoordinateSmallVFDimension

@[expose] public section

/-! A whole cell family with zero vertical paradigm has VF dimension
at most one, even when its carried RV-label set is infinite. -/
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

theorem zero_paradigm_head_value (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames)
    (ht : F.refinementParadigm hNames q = rv (0 : VF (M := M))) :
    vfAt q.val 0 = F.refinementCentre hNames q := by
  have hFibre := (F.source_head_fibre hNames q).trans
    ((congrArg (fun r => BalancedFibres.translatedRV r (F.refinementCentre hNames q)) ht).trans
      (BalancedFibres.translatedRV_zero _))
  have hReplace : replace 0 q.val (vfAt q.val 0) = q.val := Prod.ext (Function.update_eq_self 0 q.val.1) rfl
  apply (Set.ext_iff.mp hFibre (vfAt q.val 0)).mp
  change replace 0 q.val (vfAt q.val 0) ∈ carrier (gammaRVGraphRefinement A F.parameters hNames)
  rw [hReplace]
  exact q.property

set_option maxHeartbeats 800000 in
theorem zero_paradigm_dimension (hc : CanonicalStructure.IsCanonical (M := M))
    (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S)
    (ht : ∀ q : gammaRVGraphRefinement A F.parameters hNames,
      F.refinementParadigm hNames q = rv (0 : VF (M := M))) :
    SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (SpecialTransformations.Section9.rawSpecialSet hc (gammaRVGraphRefinement A F.parameters hNames)) ≤ 1 := by
  apply mixed_vf_dimension_le_one_of_coordinate hc _ 1
  intro p q hVF hRV
  have he : erase 0 p.val = erase 0 q.val := by
    apply Prod.ext
    · funext i
      fin_cases i
      · rfl
      · exact hVF
    · exact hRV
  have hCentre := F.refinement_centre_constant hNames p q he
  have hHead : vfAt p.val 0 = vfAt q.val 0 :=
    (F.zero_paradigm_head_value hNames p (ht p)).trans
      (hCentre.trans (F.zero_paradigm_head_value hNames q (ht q)).symm)
  funext i
  fin_cases i
  · exact hHead
  · exact hVF

end IntegrationInACVF.Section7.UniformMixedCellPresentation
