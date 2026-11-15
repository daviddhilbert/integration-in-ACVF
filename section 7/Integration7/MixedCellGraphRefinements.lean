import Integration7.MixedTwoCellDecomposition
import Integration7.GammaRVGraphRefinementGeometry
import IntegrationSection4.ParameterizedCells

/-! The mixed-label cell decomposition gives an actual graph refinement
whose nonempty RV-labelled fibres are definable two-cells. The graph map
retains every VF coordinate and every original RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G H : Base (M := M)} {S : Set M} {m d : ℕ}

theorem definable_two_cell_mono {R : Set (VF (M := M) × VF (M := M))}
    (hR : Cells.DefinableTwoCell G R) (hreal : G.real ⊆ H.real) (hgamma : G.gamma ⊆ H.gamma) :
    Cells.DefinableTwoCell H R := by
  obtain ⟨f,t,hCell,hPair,hf,ht,hPar⟩ := hR
  exact ⟨f,t,hCell,hPair.mono hreal hgamma,hf.mono hreal hgamma,
    ht.mono hreal hgamma,fun r hr => (hPar r hr).mono hreal hgamma⟩

theorem gamma_rv_graph_refinement_two_fibre (A : DefSet (M := M) S 2 m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S)
    (hP : ∀ a b, P.toFun a = P.toFun b → SameRV a.val b.val) (a₀ : A) :
    ParameterizedCells.twoFibre (carrier (gammaRVGraphRefinement A P hNames))
      (Fin.append a₀.val.2 (P.toFun a₀)) = mixedPairFibre P a₀ := by
  ext p
  constructor
  · rintro ⟨a,ha⟩
    have hVF := congrArg (fun q : Point (M := M) 2 (m+d) => q.1) ha
    have hTag := congrArg (fun q : Point (M := M) 2 (m+d) => q.2 ∘ Fin.natAdd m) ha
    have hTag' : P.toFun a = P.toFun a₀ := by
      funext i
      simpa only [gammaRVGraphRefinementMap,Function.comp_apply,Fin.append_right] using congrFun hTag i
    exact ⟨a,hVF,hTag'⟩
  · rintro ⟨a,ha,hTag⟩
    have hOld := ((sameRV_iff _ _).mp (hP a a₀ hTag)).2
    refine ⟨a,?_⟩
    change (a.val.1,Fin.append a.val.2 (P.toFun a)) =
      ((pairPoint p.1 p.2).1,Fin.append a₀.val.2 (P.toFun a₀))
    exact Prod.ext ha (congrArg₂ Fin.append hOld hTag)

theorem gamma_rv_graph_refinement_is_two_cell (A : DefSet (M := M) S 2 m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S)
    (hP : ∀ a b, P.toFun a = P.toFun b → SameRV a.val b.val)
    (hCells : ∀ a : A, Cells.DefinableTwoCell (RVLabelSlices.labelBase G (P.toFun a)) (mixedPairFibre P a)) :
    ParameterizedCells.DefinableTwoCell G (carrier (gammaRVGraphRefinement A P hNames)) := by
  refine ⟨gamma_rv_graph_refinement_target_gamma A P hNames,?_⟩
  intro s hne
  obtain ⟨p,hp⟩ := hne
  obtain ⟨a,ha⟩ := hp
  have hs : Fin.append a.val.2 (P.toFun a) = s :=
    congrArg (fun q : Point (M := M) 2 (m+d) => q.2) ha
  rw [← hs,gamma_rv_graph_refinement_two_fibre A P hNames hP a]
  apply definable_two_cell_mono (H := RVLabelSlices.labelBase G (Fin.append a.val.2 (P.toFun a)))
    (hCells a) ?_ (Set.Subset.refl G.gamma)
  rintro x (hx | ⟨i,rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨Fin.natAdd m i,congrArg Subtype.val (Fin.append_right a.val.2 (P.toFun a) i)⟩

theorem gamma_two_cell_graph_refinement_exists {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    (A : DefSet (M := M) S 2 m) (hA : GammaSetDefinable G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    ∃ d : ℕ, ∃ P : GammaRVMap G (carrier A) d,
      ParameterizedCells.DefinableTwoCell G (carrier (gammaRVGraphRefinement A P hNames)) := by
  obtain ⟨d,P,hP,hCells⟩ := mixed_two_cell_decomposition hκ hs h00 G hsmall hGenerated δ hδ hδ1 (carrier A) hA
  exact ⟨d,P,gamma_rv_graph_refinement_is_two_cell A P hNames hP hCells⟩

end IntegrationInACVF.Section7
