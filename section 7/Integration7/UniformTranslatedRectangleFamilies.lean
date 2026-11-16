module

public import Integration7.UniformCellRVParadigmPartitions
public import Integration7.UniformBalancedHorizontalContractions
public import Integration7.NativeRectangleFamilyStandardContractions

@[expose] public section

/-! Both actual translations of a balanced family are rectangles over
their retained RV labels. The horizontal paradigm is obtained from the
same original balanced row, rather than chosen separately at each point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

theorem rectangular_rv_fibres_of_head_saturation
    (H : Set (Point (M := M) 2 m)) (hH : HeadSaturated H)
    (hTag : ∀ p q : H, p.val.2 = q.val.2 → rv (vfAt p.val 0) = rv (vfAt q.val 0)) :
    RectangularRVFibres H := by
  apply rectangular_rv_fibres_of_mix
  intro p q hRV
  have h := hH q.val q.property (vfAt p.val 0) (hTag p q hRV)
  have he : replace 0 q.val (vfAt p.val 0) = (![vfAt p.val 0,vfAt q.val 1],p.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · exact hRV.symm
  exact (congrArg (fun z => z ∈ H) he).mp h

theorem rectangular_rv_fibres_of_tail_saturation
    (H : Set (Point (M := M) 2 m))
    (hH : ∀ p ∈ H, ∀ x : VF (M := M), rv x = rv (vfAt p 1) → replace 1 p x ∈ H)
    (hTag : ∀ p q : H, p.val.2 = q.val.2 → rv (vfAt p.val 1) = rv (vfAt q.val 1)) :
    RectangularRVFibres H := by
  apply rectangular_rv_fibres_of_mix
  intro p q hRV
  have h := hH p.val p.property (vfAt q.val 1) (hTag q p hRV.symm)
  have he : replace 1 p.val (vfAt q.val 1) = (![vfAt p.val 0,vfAt q.val 1],p.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact (congrArg (fun z => z ∈ H) he).mp h

namespace UniformMixedCellPresentation
variable {A : DefSet (M := M) S 2 m}

theorem vertical_translation_rectangular (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    RectangularRVFibres (carrier (F.verticalTranslationImage hNames)) := by
  apply rectangular_rv_fibres_of_head_saturation _ (F.vertical_translation_head_saturated hNames)
  intro p q hRV
  obtain ⟨p₀,rfl⟩ := (F.vertical_translation_bijective hNames).2 p
  obtain ⟨q₀,rfl⟩ := (F.vertical_translation_bijective hNames).2 q
  exact (F.vertical_translation_head_paradigm hNames p₀).trans
    ((F.refinement_paradigm_constant_on_labels hNames p₀ q₀ hRV).trans
      (F.vertical_translation_head_paradigm hNames q₀).symm)

set_option maxHeartbeats 1200000 in
theorem horizontal_translation_tail_paradigm
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) (a : A) (r : RV (M := M))
    (hBal : Cells.IsBalanced (mixedPairFibre F.parameters a) (F.localPosition a) r
      ((F.vertical.projection a).val.2 F.vertical.paradigm_index))
    (b : A) (hP : F.parameters.toFun b = F.parameters.toFun a) :
    rv (vfAt (F.horizontalTranslation hBalanced hNames
      (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b)).val 1) = r := by
  obtain ⟨c,hPc,hCentre⟩ := F.balanced_centre_covers_head hBalanced b
  have hCb := F.horizontal_centre_on_graph hBalanced hNames b c hPc hCentre
  have hbR : (vfAt b.val 1,vfAt b.val 0) ∈ mixedPairFibre F.parameters a := by
    refine ⟨b,?_,hP⟩
    funext i
    fin_cases i <;> rfl
  have hcR : (vfAt c.val 1,vfAt c.val 0) ∈ mixedPairFibre F.parameters a := by
    refine ⟨c,?_,hPc.trans hP⟩
    funext i
    fin_cases i <;> rfl
  have hbD : vfAt b.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := ⟨_,hbR,rfl⟩
  have hcD : vfAt c.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := ⟨_,hcR,rfl⟩
  have hPosition : F.localPosition a (vfAt c.val 1) = vfAt b.val 0 :=
    (F.centre_eq_local_position a c (hPc.trans hP)).symm.trans hCentre
  have hTag := (Set.ext_iff.mp (hBal.2.2.1.horizontal (vfAt b.val 1) hbD) (vfAt c.val 1)).mp
    ⟨hcD,by change (vfAt b.val 1,F.localPosition a (vfAt c.val 1)) ∈ mixedPairFibre F.parameters a
            rwa [hPosition]⟩
  change rv ((vfAt b.val 1)-(show VF (M := M) from (F.horizontalCentreMap hBalanced hNames
    (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b)).val 0)) = r
  rw [hCb]
  exact hTag

theorem horizontal_translation_rectangular (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S) :
    RectangularRVFibres (carrier (F.horizontalTranslationImage hBalanced hNames)) := by
  apply rectangular_rv_fibres_of_tail_saturation _
    (translated_rv_coordinate_saturated _ 1 (F.horizontalCentreMap hBalanced hNames)
      (F.horizontal_centre_constant hBalanced hNames) (F.source_horizontal_fibre hBalanced hNames))
  intro p q hRV
  obtain ⟨p₀,rfl⟩ := (F.horizontal_translation_bijective hBalanced hNames).2 p
  obtain ⟨q₀,rfl⟩ := (F.horizontal_translation_bijective hBalanced hNames).2 q
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 p₀
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q₀
  have hP : F.parameters.toFun b = F.parameters.toFun a := by
    funext j
    have h := congrFun hRV (Fin.natAdd m j)
    change Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m j) =
      Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m j) at h
    exact (Fin.append_right _ _ _).symm.trans (h.symm.trans (Fin.append_right _ _ _))
  obtain ⟨r,hBal⟩ := hBalanced a
  exact (F.horizontal_translation_tail_paradigm hBalanced hNames a r hBal a rfl).trans
    (F.horizontal_translation_tail_paradigm hBalanced hNames a r hBal b hP).symm

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
