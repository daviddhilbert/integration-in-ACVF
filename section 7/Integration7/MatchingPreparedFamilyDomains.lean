module

public import Integration7.UniformMatchingBallGeometry
public import Integration7.PreparedDifferentRectangleFamilies

@[expose] public section

/-! The matching part with both prepared keys is an actual native
family over the original common names. Its labelled rows have the proved
complete balanced geometry on the actual inverse-special balls. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)}

namespace UniformMixedCellPresentation
variable {S : Set M} {m : ℕ} {A : DefSet (M := M) S 2 m}

theorem refinement_labels_determine_same_rv (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) (p q : gammaRVGraphRefinement A F.parameters hNames)
    (hRV : p.val.2 = q.val.2) : SameRV p.val q.val := by
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 p
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A F.parameters hNames).2 q
  have hP : F.parameters.toFun a = F.parameters.toFun b := by
    funext i
    have hi := congrFun hRV (Fin.natAdd m i)
    change Fin.append a.val.2 (F.parameters.toFun a) (Fin.natAdd m i) =
      Fin.append b.val.2 (F.parameters.toFun b) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi
  have hSame := (sameRV_iff _ _).mp (F.parameters_reflect_same_rv a b hP)
  exact (sameRV_iff _ _).mpr ⟨hSame.1,hRV⟩

end UniformMixedCellPresentation

namespace UniformBalancedPositionPreparation
variable {m : ℕ} {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def matchingNative (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    DefSet (M := M) (C.base : Set M) 2 (m+F.arity) :=
  PresentedSet.mk P.matchingPart (SetDefinable.mono _
    (gamma_native_set_common_names P.matching_part_gamma) hNames)

def matchingPreparedFamily (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    DefSet (M := M) (C.base : Set M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) :=
  gammaRVGraphRefinement P.matchingNative P.matchingKeyLabels hNames

theorem matching_prepared_family_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.matchingPreparedFamily) :=
  gamma_rv_graph_refinement_target_gamma P.matchingNative P.matchingKeyLabels hNames

theorem matching_prepared_family_finite_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier P.matchingPreparedFamily}.Finite := by
  apply gamma_rv_graph_refinement_finite_labels
  intro x
  apply (gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames x).subset
  rintro r ⟨q,hq,_⟩
  exact Eq.mp (congrArg (fun p : Point (M := M) 2 (m+F.arity) =>
    p ∈ carrier (gammaRVGraphRefinement A F.parameters hNames)) hq) q.property

theorem matching_prepared_family_row (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p : P.matchingNative) :
    ParameterizedCells.twoFibre (carrier P.matchingPreparedFamily)
      (Fin.append p.val.2 (P.matchingKeyLabels.toFun p)) = mixedPairFibre P.matchingKeyLabels p := by
  apply gamma_rv_graph_refinement_two_fibre
  intro a b he
  let a₀ : gammaRVGraphRefinement A F.parameters hNames :=
    ⟨a.val,by obtain ⟨q,hq,_⟩ := a.property; exact hq ▸ q.property⟩
  let b₀ : gammaRVGraphRefinement A F.parameters hNames :=
    ⟨b.val,by obtain ⟨q,hq,_⟩ := b.property; exact hq ▸ q.property⟩
  exact F.refinement_labels_determine_same_rv hNames a₀ b₀
    (((P.pair_key_labels_iff_bodies b₀ a₀).mp he).1)

theorem matching_prepared_family_row_geometry
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (a : A)
    (hMatch : (Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a).val ∈ P.matchingPart)
    (ht : (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M))) :
    let q := Map.toImage (gammaRVGraphRefinementMap A F.parameters hNames) a
    let p : P.matchingNative := ⟨q.val,hMatch⟩
    let B := InverseOneCells.typedBody P.sourceSpecial (P.preparedTailMap q)
    let E := InverseOneCells.typedBody P.targetSpecial (P.preparedHeadMap q)
    let R := ParameterizedCells.twoFibre (carrier P.matchingPreparedFamily)
      (Fin.append p.val.2 (P.matchingKeyLabels.toFun p))
    ∃ r : RV (M := M), PaperBalls.IsOpenBall (Cells.rawSet B) ∧
      PaperBalls.IsOpenBall (Cells.rawSet E) ∧ BalancedFibres.HasBalancedFibres B E R (F.localPosition a) r
        ((F.vertical.projection a).val.2 F.vertical.paradigm_index) := by
  intro q p B E R
  have hRow := (P.matching_prepared_family_row p).trans (P.matching_key_fibre_eq p)
  change R = mixedPairFibre P.pairKeyLabels q at hRow
  rw [P.pair_key_fibre a] at hRow
  rw [hRow]
  exact P.matching_prepared_row_balanced_fibres a hMatch ht

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
