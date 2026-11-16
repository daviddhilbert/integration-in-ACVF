module

public import Integration7.MixedTwoCellDecomposition

@[expose] public section

/-! Retain the actual global positioning map behind the mixed-label
cell decomposition. Its centre depends only on the RV refinement label
and the other VF coordinate, which is the uniform translation condition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
variable {G : Base (M := M)} {A : Set (Point (M := M) 2 m)}

structure UniformMixedCellPresentation (G : Base (M := M)) (A : Set (Point (M := M) 2 m)) where
  vertical : MixedVerticalPresentation G A
  arity : ℕ
  labels : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family vertical.domain)) arity
  reflects : ∀ a b, labels.toFun a = labels.toFun b → SameRV a.val b.val
  rows : ∀ a, Nonempty (PositionRow labels a (GammaScalarFamilies.value vertical.position) vertical.paradigm_index)

namespace UniformMixedCellPresentation

def parameters (F : UniformMixedCellPresentation G A) : GammaRVMap G A F.arity := F.vertical.pullback F.labels

def centre (F : UniformMixedCellPresentation G A) (a : A) : VF (M := M) := F.vertical.position (F.vertical.projection a)

theorem parameter_cells (F : UniformMixedCellPresentation G A) :
    ∀ a : A, Cells.DefinableTwoCell (RVLabelSlices.labelBase G (F.parameters.toFun a)) (mixedPairFibre F.parameters a) :=
  F.vertical.pullback_definable_cells F.labels F.reflects F.rows

theorem parameters_reflect_same_rv (F : UniformMixedCellPresentation G A) (a b : A)
    (he : F.parameters.toFun a = F.parameters.toFun b) : SameRV a.val b.val :=
  F.vertical.inverse_rv a b (F.reflects _ _ he)

theorem centre_graph (F : UniformMixedCellPresentation G A) :
    GammaScalarGraphDefinable G (fun p z => ∃ a : A, a.val = p ∧ F.centre a = z) := by
  have h := (gammaLogicInput G).comp_graph F.vertical.projection_graph F.vertical.position_graph
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨u,⟨a,ha,hau⟩,v,hvu,hvz⟩
    have he : v = F.vertical.projection a := Subtype.ext (hvu.trans hau.symm)
    refine ⟨a,ha,?_⟩
    rw [he] at hvz
    exact hvz
  · rintro ⟨a,ha,hz⟩
    exact ⟨(F.vertical.projection a).val,⟨a,ha,rfl⟩,F.vertical.projection a,rfl,hz⟩

theorem centre_constant_on_parameter_fibres (F : UniformMixedCellPresentation G A) (a b : A)
    (he : F.parameters.toFun a = F.parameters.toFun b) (hVF : vfAt a.val 1 = vfAt b.val 1) :
    F.centre a = F.centre b := by
  have hLabels := ((sameRV_iff _ _).mp (F.reflects _ _ he)).2
  have hPoint : F.vertical.projection a = F.vertical.projection b := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (F.vertical.first a).trans (hVF.trans (F.vertical.first b).symm)
    · exact hLabels
  exact congrArg F.vertical.position hPoint

end UniformMixedCellPresentation

theorem uniform_mixed_cell_presentation_exists {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hA : GammaSetDefinable G A) : Nonempty (UniformMixedCellPresentation G A) := by
  obtain ⟨V⟩ := MixedVerticalPresentation.exists_presentation hs h00 G hsmall hGenerated A hA
  obtain ⟨d,Q,hQ,hRows⟩ := ScalarPositionDecomposition.exists_map hκ hs h00 G hsmall hGenerated γ hγ hγ1
    (GammaScalarFamilies.family V.domain) (GammaScalarFamilies.domain_vf V.domain)
    (GammaScalarFamilies.value V.position) (GammaScalarFamilies.value_vf V.position)
    (GammaScalarFamilies.graph_definable G V.domain V.position V.position_graph) V.paradigm_index
  exact ⟨⟨V,d,Q,hQ,hRows⟩⟩

end IntegrationInACVF.Section7
