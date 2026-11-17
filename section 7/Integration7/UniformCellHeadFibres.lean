module

public import Integration7.UniformCellRefinementCentres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact vertical fibres of the actual mixed cell graph refinement.
Each is the translated RV class supplied by the global positioning map;
its paradigm depends only on the retained refinement parameter. -/
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

theorem projection_eq_of_parameters_and_vf (F : UniformMixedCellPresentation G (carrier A)) (a b : A)
    (he : F.parameters.toFun a = F.parameters.toFun b) (hVF : vfAt a.val 1 = vfAt b.val 1) :
    F.vertical.projection a = F.vertical.projection b := by
  have hLabels := ((sameRV_iff _ _).mp (F.reflects _ _ he)).2
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (F.vertical.first a).trans (hVF.trans (F.vertical.first b).symm)
  · exact hLabels

def refinementParadigm (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) : RV (M := M) :=
  (F.vertical.projection (F.refinementSource hNames q)).val.2 F.vertical.paradigm_index

set_option maxHeartbeats 1200000 in
theorem source_head_fibre (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (q : gammaRVGraphRefinement A F.parameters hNames) :
    {y : VF (M := M) | replace 0 q.val y ∈ carrier (gammaRVGraphRefinement A F.parameters hNames)} =
      BalancedFibres.translatedRV (F.refinementParadigm hNames q) (F.refinementCentre hNames q) := by
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  simp only [refinementParadigm,refinementCentre,refinementSource,Map.inverse_apply]
  ext y
  constructor
  · rintro ⟨b,hb⟩
    have hP : F.parameters.toFun b = F.parameters.toFun a := by
      have ht := congrArg (fun z : Point (M := M) 2 (m+F.arity) => z.2 ∘ Fin.natAdd m) hb
      funext i
      have hi := congrFun ht i
      change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
        Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at hi
      simpa only [Fin.append_right] using hi
    have hVF : vfAt b.val 1 = vfAt a.val 1 := by
      have ht := congrArg (fun z : Point (M := M) 2 (m+F.arity) => vfAt z 1) hb
      change b.val.1 1 = Function.update a.val.1 0 y 1 at ht
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] at ht
      have hv := congrArg Subtype.val ht
      exact Subtype.ext hv
    have hHead : vfAt b.val 0 = y := by
      have ht := congrArg (fun z : Point (M := M) 2 (m+F.arity) => vfAt z 0) hb
      simpa only [gammaRVGraphRefinementMap,replace,vfAt,Function.update_self] using ht
    exact (Set.ext_iff.mp (F.vertical.fibres (F.vertical.projection a)) y).mp
      ⟨b,F.projection_eq_of_parameters_and_vf b a hP hVF,hHead⟩
  · intro hy
    obtain ⟨b,hb,hHead⟩ := (Set.ext_iff.mp (F.vertical.fibres (F.vertical.projection a)) y).mpr hy
    have hScalar : F.vertical.scalarProjection b = F.vertical.scalarProjection a := by
      have hv := congrArg Subtype.val hb
      exact Subtype.ext hv
    have hP : F.parameters.toFun b = F.parameters.toFun a := congrArg F.labels.toFun hScalar
    have hOld := ((sameRV_iff _ _).mp (F.parameters_reflect_same_rv b a hP)).2
    have hVF : vfAt b.val 1 = vfAt a.val 1 := (F.vertical.first b).symm.trans
      ((congrArg (fun z : F.vertical.domain => vfAt z.val 0) hb).trans (F.vertical.first a))
    refine ⟨b,?_⟩
    change (b.val.1,Fin.append b.val.2 (F.parameters.toFun b)) =
      replace 0 (a.val.1,Fin.append a.val.2 (F.parameters.toFun a)) y
    apply Prod.ext
    · funext i
      fin_cases i
      · exact hHead
      · change b.val.1 1 = Function.update a.val.1 0 y 1
        rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        exact hVF
    · exact congrArg₂ Fin.append hOld hP

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
