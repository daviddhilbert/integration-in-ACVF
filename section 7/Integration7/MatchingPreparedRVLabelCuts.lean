module

public import Integration7.PreparedPairFamilies
public import Integration7.GammaRVLabelCuts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Matching and different prepared families are complementary cuts
by the actual RV labels of one whole pair-key refinement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def matchingPreparedRVLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Set (Point (M := M) 0 ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))) :=
  {r | ∃ x : Fin 2 → VF (M := M), (x,r.2) ∈ carrier P.matchingPreparedFamily}

theorem matching_prepared_rv_labels_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G P.matchingPreparedRVLabels :=
  gamma_exists_vf_coordinates P.matching_prepared_family_gamma

def differentPreparedRVLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Set (Point (M := M) 0 ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))) :=
  Set.univ \ P.matchingPreparedRVLabels

theorem different_prepared_rv_labels_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G P.differentPreparedRVLabels :=
  (gammaLogicInput G).sdiff
    ((gammaLogicInput G).real_set _
      (setDefinable (PresentedSet.univ (pointSpace (M := M) 0
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity)))) G.real)))
    P.matching_prepared_rv_labels_gamma

theorem matching_prepared_mem_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (q : P.wholePreparedPairFamily) :
    q.val ∈ carrier P.matchingPreparedFamily ↔ (Fin.elim0,q.val.2) ∈ P.matchingPreparedRVLabels := by
  constructor
  · intro hq
    exact ⟨q.val.1,hq⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := q.property
    obtain ⟨b,hb⟩ := hx
    let b₀ : gammaRVGraphRefinement A F.parameters hNames :=
      ⟨b.val,by obtain ⟨p,hp,_⟩ := b.property; exact hp ▸ p.property⟩
    have hRV : Fin.append a.val.2 (P.pairKeyLabels.toFun a) =
        Fin.append b₀.val.2 (P.pairKeyLabels.toFun b₀) := by
      have h₁ := congrArg (fun p : Point (M := M) 2
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) ha
      have h₂ := congrArg (fun p : Point (M := M) 2
        ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) => p.2) hb
      exact h₁.trans h₂.symm
    have hKeys : P.pairKeyLabels.toFun a = P.pairKeyLabels.toFun b₀ := by
      funext i
      simpa only [Fin.append_right] using congrFun hRV (Fin.natAdd (m+F.arity) i)
    have hMatch := (P.matching_constant_on_pair_keys a b₀ hKeys).mpr b.property
    have hMem := (P.matching_prepared_graph_mem a).mpr hMatch
    exact Eq.mp (congrArg (fun p : Point (M := M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) =>
        p ∈ carrier P.matchingPreparedFamily) ha) hMem

theorem different_prepared_mem_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) (q : P.wholePreparedPairFamily) :
    q.val ∈ carrier P.differentPreparedFamily ↔ (Fin.elim0,q.val.2) ∈ P.differentPreparedRVLabels := by
  change q.val ∈ carrier P.differentPreparedFamily ↔
    ((Fin.elim0,q.val.2) ∈ Set.univ ∧ (Fin.elim0,q.val.2) ∉ P.matchingPreparedRVLabels)
  simp only [Set.mem_univ,true_and]
  rw [← P.matching_prepared_mem_labels q]
  obtain ⟨a,ha⟩ := q.property
  rw [← ha,P.different_prepared_graph_mem,P.matching_prepared_graph_mem]

theorem matching_prepared_eq_label_cut
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    rvLabelCut P.wholePreparedPairFamily P.whole_prepared_pair_family_gamma id
      P.matchingPreparedRVLabels P.matching_prepared_rv_labels_gamma hNames = P.matchingPreparedFamily := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨hq,hR⟩
    exact (P.matching_prepared_mem_labels ⟨q,hq⟩).mpr hR
  · intro hq
    exact ⟨P.matching_prepared_subset_whole hq,⟨q.1,hq⟩⟩

theorem different_prepared_eq_label_cut
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    rvLabelCut P.wholePreparedPairFamily P.whole_prepared_pair_family_gamma id
      P.differentPreparedRVLabels P.different_prepared_rv_labels_gamma hNames = P.differentPreparedFamily := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨hq,hR⟩
    exact (P.different_prepared_mem_labels ⟨q,hq⟩).mpr hR
  · intro hq
    exact ⟨P.different_prepared_subset_whole hq,
      (P.different_prepared_mem_labels ⟨q,P.different_prepared_subset_whole hq⟩).mp hq⟩

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
