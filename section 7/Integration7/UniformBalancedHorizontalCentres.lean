module

public import Integration7.UniformBalancedPositionMaps
public import IntegrationSection5.ScalarCoordinateRefinement
public import IntegrationSection5.NaturalContractionMap

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An actual inverse mixed positioning map supplies the horizontal
centre of a balanced family. It preserves the full original-Gamma graph
and depends only on the head VF coordinate and all refined RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m : ℕ}

theorem gamma_native_coordinate_project_graph (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A)) (i : Fin n) :
    GammaGraphDefinable G (pointMapGraph (coordinateProjectMap i A)) := by
  let Q := mixedCoordinatePointMap (fun _ : Fin 1 => i) (id : Fin m → Fin m) G.real
  have h := (gammaLogicInput G).restrict_graph hA ((gammaLogicInput G).real_map_graph Q)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,u,rfl,hq⟩
    exact ⟨⟨u.val,hp⟩,rfl,hq⟩
  · rintro ⟨u,rfl,hu⟩
    exact ⟨u.property,⟨u.val,Set.mem_univ _⟩,rfl,hu⟩

namespace UniformMixedCellPresentation
variable {A : DefSet (M := M) S 2 m}

def headToPositionImage (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) :
    Map (gammaRVGraphRefinement A F.parameters hNames) (F.positionImage hNames) :=
  mapIntoSubset (coordinateProjectMap 0 _) (F.positionImage hNames) (F.position_image_covers_head hBalanced hNames)

def horizontalCentreMap (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) :
    Map (gammaRVGraphRefinement A F.parameters hNames)
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.comp (firstVFMap _)
    (Map.comp (Map.inverse (Map.toImage (F.positionMap hNames)) (F.position_to_image_bijective hBalanced hNames))
      (F.headToPositionImage hBalanced hNames))

theorem head_to_position_image_gamma (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) :
    GammaGraphDefinable G (pointMapGraph (F.headToPositionImage hBalanced hNames)) :=
  gamma_native_coordinate_project_graph _ (gamma_rv_graph_refinement_target_gamma A F.parameters hNames) 0

theorem horizontal_centre_graph_gamma (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) :
    GammaScalarGraphDefinable G (fun p z => ∃ q : gammaRVGraphRefinement A F.parameters hNames,
      q.val = p ∧ (F.horizontalCentreMap hBalanced hNames q).val 0 = z) := by
  let f := Map.toImage (F.positionMap hNames)
  let hf := F.position_to_image_bijective hBalanced hNames
  let g := Map.comp (Map.inverse f hf) (F.headToPositionImage hBalanced hNames)
  have hInv := gamma_inverse_map_graph f hf (F.position_map_gamma hNames)
  have hGamma := gamma_composition_graph (F.headToPositionImage hBalanced hNames) (Map.inverse f hf)
    (F.head_to_position_image_gamma hBalanced hNames) hInv
  exact gamma_scalar_coordinate g hGamma 0

theorem horizontal_centre_constant (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S) (p q : gammaRVGraphRefinement A F.parameters hNames)
    (he : erase 1 p.val = erase 1 q.val) :
    (F.horizontalCentreMap hBalanced hNames p).val 0 = (F.horizontalCentreMap hBalanced hNames q).val 0 := by
  have hLabels := congrArg (fun z : Point (M := M) 2 (m+F.arity) => z.2) he
  have hHead := congrArg (fun z : Point (M := M) 2 (m+F.arity) => vfAt z 0) he
  simp only [erase,replace,vfAt,Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at hHead
  have hInput : F.headToPositionImage hBalanced hNames p = F.headToPositionImage hBalanced hNames q := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact hHead
    · exact hLabels
  exact congrArg (fun z : F.positionImage hNames =>
    (firstVFMap _ (Map.inverse (Map.toImage (F.positionMap hNames))
      (F.position_to_image_bijective hBalanced hNames) z)).val 0) hInput

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
