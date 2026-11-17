module

public import Integration7.GammaNativeCommonNames
public import Integration7.GammaRVLabelFocusLifts
public import IntegrationSection4.GammaRVMapOperations
public import IntegrationSection4.GammaOffsets

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A Gamma RV map gives an actual VF-preserving graph refinement.
Every old RV coordinate is retained literally, and the full graph stays
over the original Gamma base. -/
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
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m d : ℕ}

set_option maxHeartbeats 800000 in
theorem gamma_rv_graph_refinement_graph (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) :
    GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) n (m+d)) =>
      ∃ a : A, a.val = p ∧ (a.val.1,Fin.append a.val.2 (P.toFun a)) = q) := by
  let X := PresentedSet.univ (pointSpace (M := M) n (m+d)) G.real
  let K := Map.comp (GammaOffsets.dropVFMap G.real n d)
    (retainVFLabelsMap (Fin.natAdd m : Fin d → Fin (m+d)) X)
  let L := retainVFLabelsMap (Fin.castAdd d : Fin m → Fin (m+d)) X
  have hTags := (gammaLogicInput G).comp_graph P.graph
    ((gammaLogicInput G).swap_graph ((gammaLogicInput G).real_map_graph K))
  have hOld := (gammaLogicInput G).swap_graph ((gammaLogicInput G).real_map_graph L)
  apply GammaGraphDefinable.congr (GammaGraphOperations.inter G hTags hOld)
  intro p q
  constructor
  · rintro ⟨⟨r,⟨a,ha,hr⟩,b,hb,hbr⟩,c,hc,hcp⟩
    have hbq : b.val = q := hb
    have hcq : c.val = q := hc
    have htag : P.toFun a = q.2 ∘ Fin.natAdd m := by
      have he := congrArg (fun z : Point (M := M) 0 d => z.2) hbr
      change b.val.2 ∘ Fin.natAdd m = r.2 at he
      exact hr.trans (he.symm.trans (congrArg (fun z : Point (M := M) n (m+d) => z.2 ∘ Fin.natAdd m) hbq))
    have hold : retainVFLabels (Fin.castAdd d) q = p := by
      change retainVFLabels (Fin.castAdd d) c.val = p at hcp
      exact hcq ▸ hcp
    refine ⟨a,ha,?_⟩
    have hpa := hold.trans ha.symm
    apply Prod.ext
    · exact (congrArg (fun z : Point (M := M) n m => z.1) hpa).symm
    · change Fin.append a.val.2 (P.toFun a) = q.2
      rw [htag,← congrArg (fun z : Point (M := M) n m => z.2) hpa]
      exact Fin.append_castAdd_natAdd
  · rintro ⟨a,ha,rfl⟩
    refine ⟨⟨(Fin.elim0,P.toFun a),⟨a,ha,rfl⟩,⟨(a.val.1,Fin.append a.val.2 (P.toFun a)),Set.mem_univ _⟩,rfl,?_⟩,
      ⟨(a.val.1,Fin.append a.val.2 (P.toFun a)),Set.mem_univ _⟩,rfl,?_⟩
    · apply Prod.ext (Subsingleton.elim _ _)
      funext i
      exact Fin.append_right _ _ i
    · change (a.val.1,Fin.append a.val.2 (P.toFun a) ∘ Fin.castAdd d) = p
      apply Prod.ext
      · have he := congrArg (fun z : Point (M := M) n m => z.1) ha
        exact he
      · exact (funext fun i => Fin.append_left _ _ i).trans
          (congrArg (fun z : Point (M := M) n m => z.2) ha)

def gammaRVGraphRefinementMap (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    Map A (PresentedSet.univ (pointSpace n (m+d)) S) := by
  refine @SpecialTransformations.DefinableGeometry.Map.mk LRV M (CanonicalStructure.normalize (M := M))
    _ _ S A (PresentedSet.univ (pointSpace n (m+d)) S)
    (fun a => ⟨(a.val.1,Fin.append a.val.2 (P.toFun a)),Set.mem_univ _⟩) ?_
  exact RelationDefinable.mono _ _
    (gamma_native_graph_common_names (gamma_rv_graph_refinement_graph A P)) hNames

theorem gamma_rv_graph_refinement_map_gamma (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    GammaGraphDefinable G (pointMapGraph (gammaRVGraphRefinementMap A P hNames)) :=
  gamma_rv_graph_refinement_graph A P

theorem gamma_rv_graph_refinement_injective (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) :
    Function.Injective (gammaRVGraphRefinementMap A P hNames) := by
  intro a b he
  have hv := congrArg (fun q : PresentedSet.univ (pointSpace n (m+d)) S => q.val) he
  apply Subtype.ext
  apply Prod.ext
  · have he := congrArg (fun q : Point (M := M) n (m+d) => q.1) hv
    exact he
  · funext i
    have hi := congrArg (fun q : Point (M := M) n (m+d) => q.2 (Fin.castAdd d i)) hv
    simpa only [gammaRVGraphRefinementMap,Fin.append_left] using hi

theorem gamma_rv_graph_refinement_retains_labels (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S) (a : A) :
    retainVFLabels (Fin.castAdd d) (gammaRVGraphRefinementMap A P hNames a).val = a.val := by
  refine Prod.ext rfl ?_
  funext i
  exact Fin.append_left _ _ i

end IntegrationInACVF.Section7
