import Integration7.UniformCellRefinementCentres
import Integration7.GammaScalarMapDescent
import IntegrationSection6.MixedCoordinatePointMaps

/-! The uniform cell centre descends to an actual mixed unary map of
the other VF coordinate and all refinement labels, over the original
Gamma base. This is the family positioning map needed for the inverse
horizontal centre in balanced cells. -/
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
open IntegrationInACVF.Section4 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m : ℕ}

theorem gamma_native_tail_key_graph (A : DefSet (M := M) S (n+1) m)
    (hA : GammaSetDefinable G (carrier A)) : GammaGraphDefinable G (pointMapGraph (VerticalOffsets.keyMap A)) := by
  let Q := mixedCoordinatePointMap (Fin.succ : Fin n → Fin (n+1)) (id : Fin m → Fin m) G.real
  have h := (gammaLogicInput G).restrict_graph hA ((gammaLogicInput G).real_map_graph Q)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,u,rfl,hq⟩
    exact ⟨⟨u.val,hp⟩,rfl,hq⟩
  · rintro ⟨u,rfl,hu⟩
    exact ⟨u.property,⟨u.val,Set.mem_univ _⟩,rfl,hu⟩

private theorem centre_constant_on_tail_key {l : ℕ} (A : DefSet (M := M) S 2 l)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hC : ∀ p q : A, erase 0 p.val = erase 0 q.val → (c p).val 0 = (c q).val 0)
    (p q : A) (he : VerticalOffsets.keyMap A p = VerticalOffsets.keyMap A q) : c p = c q := by
  have hk := congrArg Subtype.val he
  have hErase : erase 0 p.val = erase 0 q.val := by
    apply Prod.ext
    · funext i
      fin_cases i
      · rfl
      · have ht := congrArg (fun z : Point (M := M) 1 l => vfAt z 0) hk
        exact ht
    · exact congrArg (fun z : Point (M := M) 1 l => z.2) hk
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hC p q hErase

namespace UniformMixedCellPresentation
variable {A : DefSet (M := M) S 2 m}

def tailPositionMap (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    Map (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames))
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  nativeScalarDescent (VerticalOffsets.keyMap _) (F.refinementCentreMap hNames)
    (centre_constant_on_tail_key _ _ (F.refinement_centre_constant hNames))

theorem tail_position_map_value (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (p : gammaRVGraphRefinement A F.parameters hNames) :
    F.tailPositionMap hNames (VerticalOffsets.toKey _ p) = F.refinementCentreMap hNames p :=
  native_scalar_descent_value _ _ _ p

theorem tail_position_graph_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    GammaScalarGraphDefinable G (fun p z =>
      ∃ q : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames),
        q.val = p ∧ (F.tailPositionMap hNames q).val 0 = z) :=
  gamma_native_scalar_descent_graph _ _ _
    (gamma_native_tail_key_graph _ (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))
    (F.refinement_centre_gamma hNames)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
