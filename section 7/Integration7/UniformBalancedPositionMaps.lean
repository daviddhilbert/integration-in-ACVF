import Integration7.UniformBalancedCellGeometry
import Integration7.UniformCellTailPositions
import Integration7.NativeScalarReplacementMaps

/-! The mixed unary positioning map of a balanced cell family is an
actual original-Gamma bijection onto its image, retaining all RV labels.
Its image contains every labelled head projection of the full family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

namespace UniformMixedCellPresentation

def positionMap (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Map (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames))
      (PresentedSet.univ (pointSpace 1 (m+F.arity)) S) :=
  nativeScalarReplacementMap _ 0 (F.tailPositionMap hNames)

def positionImage (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S 1 (m+F.arity) := Map.image (F.positionMap hNames)

set_option maxHeartbeats 800000 in
theorem position_map_on_graph (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (a : A) :
    (F.positionMap hNames (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a))).val =
      (fun _ : Fin 1 => F.centre a,Fin.append a.val.2 (F.parameters.toFun a)) := by
  have h := F.tail_position_map_value hNames (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)
  have hv := congrArg (fun z : PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S => z.val 0) h
  change (F.tailPositionMap hNames (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a))).val 0 =
    F.centre (Map.inverse (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames))
      (gamma_rv_graph_refinement_bijective A F.parameters hNames)
      (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)) at hv
  rw [Map.inverse_apply] at hv
  change replace 0 _ _ = _
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hv
  · rfl

set_option maxHeartbeats 1200000 in
theorem position_map_injective (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : Function.Injective (F.positionMap hNames) := by
  intro p q he
  obtain ⟨pH,hp⟩ := p.property
  obtain ⟨qH,hq⟩ := q.property
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 pH
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 qH
  have hp' : p = VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a) := Subtype.ext hp.symm
  have hq' : q = VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b) := Subtype.ext hq.symm
  subst p
  subst q
  have hv := congrArg Subtype.val he
  have hData := (F.position_map_on_graph hNames a).symm.trans (hv.trans (F.position_map_on_graph hNames b))
  clear hv
  have hv := hData
  have hCentre : F.centre a = F.centre b := congrArg (fun z : Point (M := M) 1 (m+F.arity) => vfAt z 0) hv
  have hLabels := congrArg (fun z : Point (M := M) 1 (m+F.arity) => z.2) hv
  have hP : F.parameters.toFun b = F.parameters.toFun a := by
    funext i
    have ht := congrFun hLabels (Fin.natAdd m i)
    simpa only [Fin.append_right] using ht.symm
  have hVF := F.balanced_centre_injective hBalanced a b hP hCentre
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hVF
  · exact hLabels

theorem position_map_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaGraphDefinable G (pointMapGraph (F.positionMap hNames)) :=
  gamma_native_scalar_replacement_graph _ 0 (F.tailPositionMap hNames) (F.tail_position_graph_gamma hNames)

theorem position_to_image_bijective (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) : Function.Bijective (Map.toImage (F.positionMap hNames)) :=
  native_scalar_replacement_to_image_bijective _ 0 (F.tailPositionMap hNames) (F.position_map_injective hBalanced hNames)

set_option maxHeartbeats 800000 in
theorem position_image_covers_head (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    (fun _ : Fin 1 => vfAt q.val 0,q.val.2) ∈ carrier (F.positionImage hNames) := by
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  obtain ⟨b,hPb,hCentre⟩ := F.balanced_centre_covers_head hBalanced a
  have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hPb)).2
  refine ⟨VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b),?_⟩
  refine (F.position_map_on_graph hNames b).trans ?_
  change (fun _ : Fin 1 => F.centre b,Fin.append b.val.2 (F.parameters.toFun b)) =
    (fun _ : Fin 1 => vfAt a.val 0,Fin.append a.val.2 (F.parameters.toFun a))
  apply Prod.ext
  · funext i
    exact hCentre
  · exact congrArg₂ Fin.append hOld hPb

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
