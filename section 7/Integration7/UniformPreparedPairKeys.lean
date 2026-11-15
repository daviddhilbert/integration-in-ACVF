import Integration7.UniformPreparedPositionLabelMaps
import IntegrationSection5.RVCodePredicates

/-! Record both actual prepared unary keys on the original cell graph.
Equality with the prepared positioning key defines the matching part
over the unchanged Gamma base. -/
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
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaRVKeysOfMap {G : Base (M := M)} {S : Set M} {n m u w : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaRVMap G (carrier A) (u+w) where
  toFun a := (GammaRVMap.keyPointMap G.real u w ⟨(f a).val,Set.mem_univ _⟩).val.2
  graph := by
    have h := (gammaLogicInput G).comp_graph hf
      ((gammaLogicInput G).real_map_graph (GammaRVMap.keyPointMap G.real u w))
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨z,⟨a,ha,hz⟩,v,hv,hq⟩
      have he : v = ⟨(f a).val,Set.mem_univ _⟩ := Subtype.ext (hv.trans hz.symm)
      rw [he] at hq
      exact ⟨a,ha,congrArg Prod.snd hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨(f a).val,⟨a,ha,rfl⟩,⟨(f a).val,Set.mem_univ _⟩,rfl,
        Prod.ext (Subsingleton.elim _ _) hq⟩

theorem flattened_key_eq_iff_same_rv {n m : ℕ} (p q : Point (M := M) n m) :
    Fin.append (fun i => rv (vfAt p i)) p.2 = Fin.append (fun i => rv (vfAt q i)) q.2 ↔
      SameRV p q := by
  constructor
  · intro h
    apply (sameRV_iff p q).mpr
    constructor
    · intro i
      exact (Fin.append_left _ _ i).symm.trans
        ((congrFun h (Fin.castAdd m i)).trans (Fin.append_left _ _ i))
    · funext j
      exact (Fin.append_right _ _ j).symm.trans
        ((congrFun h (Fin.natAdd n j)).trans (Fin.append_right _ _ j))
  · intro h
    obtain ⟨hV,hRV⟩ := (sameRV_iff p q).mp h
    exact congrArg₂ Fin.append (funext hV) hRV

theorem gamma_rv_keys_of_map_value {G : Base (M := M)} {S : Set M} {n m u w : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) (a : A) :
    (gammaRVKeysOfMap f hf).toFun a = Fin.append (fun i => rv (vfAt (f a).val i)) (f a).val.2 := rfl

namespace UniformBalancedPositionPreparation
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def preparedTailMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map (extendBase (gammaRVGraphRefinement A F.parameters hNames) P.baseInclusion) P.source :=
  Map.comp P.sourceSpecial.toMap
    (@SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _
      (C.base : Set M) (P.context.base : Set M) _ _
      (Map.toImage (VerticalOffsets.keyMap (gammaRVGraphRefinement A F.parameters hNames))) P.baseInclusion)

def preparedHeadMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Map (extendBase (gammaRVGraphRefinement A F.parameters hNames) P.baseInclusion) P.target :=
  Map.comp P.targetSpecial.toMap
    (@SpecialTransformations.DefinableGeometry.Map.extend LRV M N _ _
      (C.base : Set M) (P.context.base : Set M) _ _
      (F.headToPositionImage hBalanced hNames) P.baseInclusion)

theorem prepared_tail_graph_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.preparedTailMap) :=
  gamma_composition_graph _ _
    (gamma_native_tail_key_graph _ (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))
    (GammaChainDefinable.graph (gammaLogicInput G) P.sourceSpecial.chain P.sourceGamma)

theorem prepared_head_graph_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (pointMapGraph P.preparedHeadMap) :=
  gamma_composition_graph _ _ (F.head_to_position_image_gamma hBalanced hNames)
    (GammaChainDefinable.graph (gammaLogicInput G) P.targetSpecial.chain P.targetGamma)

def tailKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G (carrier (gammaRVGraphRefinement A F.parameters hNames)) (1+P.sourceArity) := by
  let Q := gammaRVKeysOfMap P.preparedTailMap P.prepared_tail_graph_gamma
  exact Q

def headKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G (carrier (gammaRVGraphRefinement A F.parameters hNames)) (1+P.targetArity) := by
  let Q := gammaRVKeysOfMap P.preparedHeadMap P.prepared_head_graph_gamma
  exact Q

def positionKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G (carrier (gammaRVGraphRefinement A F.parameters hNames)) (1+P.targetArity) := by
  let Q := gammaRVKeysOfMap (Map.comp P.conjugateMap P.preparedTailMap)
    (gamma_composition_graph _ _ P.prepared_tail_graph_gamma P.conjugateGamma)
  exact Q

def pairKeyLabels (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaRVMap G (carrier (gammaRVGraphRefinement A F.parameters hNames))
      ((1+P.sourceArity)+(1+P.targetArity)) := P.tailKeyLabels.pair P.headKeyLabels

def matchingPart (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Set (Point (M := M) 2 (m+F.arity)) := rvCodeEqualizer P.headKeyLabels P.positionKeyLabels

theorem matching_part_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G P.matchingPart := rvCodeEqualizer_definable _ _

def differentPart (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Set (Point (M := M) 2 (m+F.arity)) :=
  carrier (gammaRVGraphRefinement A F.parameters hNames) \ P.matchingPart

theorem different_part_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G P.differentPart := (gammaLogicInput G).sdiff
      (gamma_rv_graph_refinement_target_gamma A F.parameters hNames) P.matching_part_gamma

theorem matching_different_partition (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Disjoint P.matchingPart P.differentPart ∧ P.matchingPart ∪ P.differentPart =
      carrier (gammaRVGraphRefinement A F.parameters hNames) := by
  have hSub : P.matchingPart ⊆ carrier (gammaRVGraphRefinement A F.parameters hNames) := by
    rintro p ⟨a,ha,_⟩
    exact ha ▸ a.property
  exact ⟨Set.disjoint_sdiff_right,Set.union_sdiff_cancel hSub⟩

theorem matching_part_mem (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (q : gammaRVGraphRefinement A F.parameters hNames) :
    q.val ∈ P.matchingPart ↔ SameRV (P.preparedHeadMap q).val
      (P.conjugateMap (P.preparedTailMap q)).val := by
  have hKey : P.headKeyLabels.toFun q = P.positionKeyLabels.toFun q ↔
      SameRV (P.preparedHeadMap q).val (P.conjugateMap (P.preparedTailMap q)).val :=
    flattened_key_eq_iff_same_rv _ _
  constructor
  · rintro ⟨a,ha,he⟩
    have haq : a = q := Subtype.ext ha
    subst a
    exact hKey.mp he
  · intro h
    exact ⟨q,rfl,hKey.mpr h⟩

theorem pair_key_labels_same (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : gammaRVGraphRefinement A F.parameters hNames)
    (he : P.pairKeyLabels.toFun p = P.pairKeyLabels.toFun q) :
    SameRV (P.preparedTailMap p).val (P.preparedTailMap q).val ∧
      SameRV (P.preparedHeadMap p).val (P.preparedHeadMap q).val := by
  have hT : P.tailKeyLabels.toFun p = P.tailKeyLabels.toFun q := by
    funext i
    exact (Fin.append_left _ _ i).symm.trans
      ((congrFun he (Fin.castAdd (1+P.targetArity) i)).trans (Fin.append_left _ _ i))
  have hH : P.headKeyLabels.toFun p = P.headKeyLabels.toFun q := by
    funext i
    exact (Fin.append_right _ _ i).symm.trans
      ((congrFun he (Fin.natAdd (1+P.sourceArity) i)).trans (Fin.append_right _ _ i))
  exact ⟨(flattened_key_eq_iff_same_rv _ _).mp hT,(flattened_key_eq_iff_same_rv _ _).mp hH⟩

theorem matching_constant_on_pair_keys (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (p q : gammaRVGraphRefinement A F.parameters hNames)
    (he : P.pairKeyLabels.toFun p = P.pairKeyLabels.toFun q) :
    p.val ∈ P.matchingPart ↔ q.val ∈ P.matchingPart := by
  obtain ⟨hT,hH⟩ := P.pair_key_labels_same p q he
  have hP := P.forwardContractible (P.preparedTailMap p) (P.preparedTailMap q) hT
  rw [P.matching_part_mem p,P.matching_part_mem q]
  exact ⟨fun h => hH.symm.trans (h.trans hP),fun h => hH.trans (h.trans hP.symm)⟩

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
