module

public import Integration7.UniformBalancedGammaLinearity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Labelwise Gamma-linearity is transferred from the actual cell
rows to the one global native positioning map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

theorem position_map_gamma_linear_of_centre
    (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S)
    (a : A) (s : Values.Gamma (M := M))
    (hLin : ∀ b c : A, F.parameters.toFun b = F.parameters.toFun a → F.parameters.toFun c = F.parameters.toFun a →
      Values.vfValueHom (F.centre c-F.centre b) = s.val*Values.vfValueHom (vfAt c.val 1-vfAt b.val 1)) :
    ∀ x y : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames),
      x.val.2 = (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).val.2 →
      y.val.2 = (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).val.2 →
      Values.vfValueHom (vfAt (F.positionMap hNames y).val 0-vfAt (F.positionMap hNames x).val 0) =
        s.val*Values.vfValueHom (vfAt y.val 0-vfAt x.val 0) := by
  intro x y hx hy
  obtain ⟨b,rfl⟩ := F.tail_key_source hNames x
  obtain ⟨c,rfl⟩ := F.tail_key_source hNames y
  have hP (b : A)
      (h : (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) b)).val.2 =
        (VerticalOffsets.toKey _ (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a)).val.2) :
      F.parameters.toFun b = F.parameters.toFun a := by
    funext i
    have hi := congrFun h (Fin.natAdd m i)
    change Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) =
      Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi
  have hB := congrArg (fun z : Point (M := M) 1 (m+F.arity) => vfAt z 0) (F.position_map_on_graph hNames b)
  have hC := congrArg (fun z : Point (M := M) 1 (m+F.arity) => vfAt z 0) (F.position_map_on_graph hNames c)
  have hDiff := congrArg₂ (fun u v : VFType (M := M) => Values.vfValueHom (u-v)) hC hB
  exact hDiff.trans (hLin b c (hP b hx) (hP c hy))

theorem position_map_gamma_linear_on_label_fibre
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNames : commonRealNames G ⊆ S)
    (p : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) :
    ∃ s : Values.Gamma (M := M), ∀ x y : VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames),
      x.val.2 = p.val.2 → y.val.2 = p.val.2 →
      Values.vfValueHom (vfAt (F.positionMap hNames y).val 0-vfAt (F.positionMap hNames x).val 0) =
        s.val*Values.vfValueHom (vfAt y.val 0-vfAt x.val 0) := by
  obtain ⟨a,rfl⟩ := F.tail_key_source hNames p
  obtain ⟨s,hLin⟩ := F.balanced_centre_gamma_linear_on_parameter_fibre hBalanced a
  exact ⟨s,F.position_map_gamma_linear_of_centre hNames a s hLin⟩

end IntegrationInACVF.Section7.UniformMixedCellPresentation
