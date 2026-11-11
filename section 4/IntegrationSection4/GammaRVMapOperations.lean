import IntegrationSection4.GammaRVMaps
import IntegrationSection4.GammaGraphOperations

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d e : ℕ} {A : Set (Point (M := M) n m)}

def pair (P : GammaRVMap G A d) (Q : GammaRVMap G A e) : GammaRVMap G A (d+e) where
  toFun a := Fin.append (P.toFun a) (Q.toFun a)
  graph := by
    have h := GammaGraphOperations.inter G
      (GammaGraphOperations.reindex_rv_output G P.graph (Fin.castAdd e))
      (GammaGraphOperations.reindex_rv_output G Q.graph (Fin.natAdd d))
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨⟨a,ha,hp⟩,b,hb,hq⟩
      have hab : b = a := Subtype.ext (hb.trans ha.symm)
      subst b
      refine ⟨a,ha,funext fun i => ?_⟩
      cases i using Fin.addCases with
      | left i => simpa only [Fin.append_left,Function.comp_apply] using congrFun hp i
      | right i => simpa only [Fin.append_right,Function.comp_apply] using congrFun hq i
    · rintro ⟨a,ha,he⟩
      refine ⟨⟨a,ha,?_⟩,a,ha,?_⟩
      · funext i
        have hh := congrFun he (Fin.castAdd e i)
        simpa only [Fin.append_left,Function.comp_apply] using hh
      · funext i
        have hh := congrFun he (Fin.natAdd d i)
        simpa only [Fin.append_right,Function.comp_apply] using hh

def precomp {u w : ℕ} {C : Set (Point (M := M) u w)} (P : GammaRVMap G C d)
    (H : A → C)
    (hH : GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) u w) =>
      ∃ a : A, a.val = p ∧ (H a).val = q)) : GammaRVMap G A d where
  toFun a := P.toFun (H a)
  graph := by
    have h := (gammaLogicInput G).comp_graph hH P.graph
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨z,⟨a,ha,hz⟩,c,hc,he⟩
      have hca : c = H a := Subtype.ext (hc.trans hz.symm)
      exact ⟨a,ha,hca ▸ he⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨(H a).val,⟨a,ha,rfl⟩,H a,rfl,he⟩

def ofReal (G : GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A)
    (f : Map (PresentedSet.univ (pointSpace n m) G.real)
      (PresentedSet.univ (pointSpace 0 d) G.real)) : GammaRVMap G A d where
  toFun a := (f ⟨a.val,Set.mem_univ _⟩).val.2
  graph := by
    have h := (gammaLogicInput G).restrict_graph hA ((gammaLogicInput G).real_map_graph f)
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨hp,b,hb,hq⟩
      have hb' : b = ⟨p,Set.mem_univ _⟩ := Subtype.ext hb
      rw [hb'] at hq
      exact ⟨⟨p,hp⟩,rfl,congrArg Prod.snd hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,Prod.ext (Subsingleton.elim _ _) hq⟩

def zero (G : GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (d : ℕ) : GammaRVMap G A d :=
  ofReal G A hA (constantRVMap (PresentedSet.univ (pointSpace n m) G.real) d)

def union {D : Set (Point (M := M) n m)} (P : GammaRVMap G A d) (Q : GammaRVMap G D d)
    (hAD : Disjoint A D) : GammaRVMap G (A ∪ D) d where
  toFun a := if h : a.val ∈ A then P.toFun ⟨a.val,h⟩ else Q.toFun ⟨a.val,a.property.resolve_left h⟩
  graph := by
    have h := (gammaLogicInput G).union_graph P.graph Q.graph
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro (⟨a,ha,he⟩ | ⟨a,ha,he⟩)
      · refine ⟨⟨a.val,Or.inl a.property⟩,ha,?_⟩
        rw [dif_pos a.property]
        exact he
      · have hn : a.val ∉ A := fun h => Set.disjoint_left.mp hAD h a.property
        refine ⟨⟨a.val,Or.inr a.property⟩,ha,?_⟩
        rw [dif_neg hn]
        exact he
    · rintro ⟨a,ha,he⟩
      by_cases hm : a.val ∈ A
      · rw [dif_pos hm] at he
        exact Or.inl ⟨⟨a.val,hm⟩,ha,he⟩
      · rw [dif_neg hm] at he
        exact Or.inr ⟨⟨a.val,a.property.resolve_left hm⟩,ha,he⟩

end IntegrationInACVF.Section4.GammaRVMap
