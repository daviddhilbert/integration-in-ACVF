module

public import Integration7.UniformMixedCellPresentations
public import Integration7.NativeRVGraphVolumeRefinements
public import Integration7.NativeRelativeTranslations

@[expose] public section

/-! The global cell positioning function is an actual original-Gamma
centre on the graph refinement. It is constant when the other VF
coordinate and every refined RV label are fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
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

def refinementSource (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S)
    (q : gammaRVGraphRefinement A F.parameters hNames) : A :=
  Map.inverse (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames))
    (gamma_rv_graph_refinement_bijective A F.parameters hNames) q

theorem refinement_source_value (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    (F.refinementSource hNames q).val = retainVFLabels (Fin.castAdd F.arity) q.val :=
  native_rv_graph_refinement_inverse_value A F.parameters hNames q

theorem refinement_source_parameters (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    F.parameters.toFun (F.refinementSource hNames q) = q.val.2 ∘ Fin.natAdd m := by
  have he := Map.apply_inverse (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames))
    (gamma_rv_graph_refinement_bijective A F.parameters hNames) q
  have hv := congrArg (fun z : gammaRVGraphRefinement A F.parameters hNames => z.val.2 ∘ Fin.natAdd m) he
  funext i
  have hi := congrFun hv i
  change Fin.append (F.refinementSource hNames q).val.2 (F.parameters.toFun (F.refinementSource hNames q))
    (Fin.natAdd m i) = q.val.2 (Fin.natAdd m i) at hi
  rw [Fin.append_right] at hi
  have hval := congrArg Subtype.val hi
  exact Subtype.ext hval

def refinementCentre (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) : VF (M := M) :=
  F.centre (F.refinementSource hNames q)

theorem refinement_centre_gamma (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    GammaScalarGraphDefinable G (fun p z => ∃ q : gammaRVGraphRefinement A F.parameters hNames,
      q.val = p ∧ F.refinementCentre hNames q = z) := by
  let f := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames)
  let hf := gamma_rv_graph_refinement_bijective A F.parameters hNames
  have h := (gammaLogicInput G).comp_graph
    ((gammaLogicInput G).swap_graph (gamma_rv_graph_refinement_map_gamma A F.parameters hNames)) F.centre_graph
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,hap⟩,b,hbz,hbzv⟩
    have hba : b = a := Subtype.ext (hbz.trans ha.symm)
    refine ⟨f a,hap,?_⟩
    change F.centre (Map.inverse f hf (f a)) = _
    rw [Map.inverse_apply]
    rw [hba] at hbzv
    exact hbzv
  · rintro ⟨u,hu,huz⟩
    let a := F.refinementSource hNames u
    refine ⟨a.val,⟨a,rfl,?_⟩,a,rfl,huz⟩
    have he := Map.apply_inverse f hf u
    have hv := congrArg Subtype.val he
    exact hv.trans hu

set_option maxHeartbeats 800000 in
def refinementCentreMap (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    Map (gammaRVGraphRefinement A F.parameters hNames)
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) := by
  refine @SpecialTransformations.DefinableGeometry.Map.mk LRV M (CanonicalStructure.normalize (M := M))
    _ _ S _ _ (fun q => ⟨fun _ => F.refinementCentre hNames q,Set.mem_univ _⟩) ?_
  have h := RelationDefinable.mono _ _ (gamma_native_scalar_common_names (F.refinement_centre_gamma hNames)) hNames
  apply @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.congr LRV M
    (CanonicalStructure.normalize (M := M)) _ _ S _ _ h
  intro p z
  constructor
  · rintro ⟨q,hq,hqz⟩
    refine ⟨q,hq,funext fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hqz
  · rintro ⟨q,hq,hqz⟩
    exact ⟨q,hq,congrFun hqz 0⟩

theorem refinement_centre_constant (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (p q : gammaRVGraphRefinement A F.parameters hNames)
    (he : erase 0 p.val = erase 0 q.val) :
    (F.refinementCentreMap hNames p).val 0 = (F.refinementCentreMap hNames q).val 0 := by
  have hLabels := congrArg (fun z : Point (M := M) 2 (m+F.arity) => z.2) he
  have hVF := congrArg (fun z : Point (M := M) 2 (m+F.arity) => vfAt z 1) he
  simp only [erase,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] at hVF
  apply F.centre_constant_on_parameter_fibres
  · rw [F.refinement_source_parameters,F.refinement_source_parameters]
    exact congrArg (fun r => r ∘ Fin.natAdd m) hLabels
  · have hp := congrArg (fun z : Point (M := M) 2 m => vfAt z 1) (F.refinement_source_value hNames p)
    have hq := congrArg (fun z : Point (M := M) 2 m => vfAt z 1) (F.refinement_source_value hNames q)
    exact hp.trans (hVF.trans hq.symm)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
