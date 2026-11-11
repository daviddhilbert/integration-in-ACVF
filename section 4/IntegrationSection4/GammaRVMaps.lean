import IntegrationSection4.FamilyPositionRefinement
import IntegrationSection4.GammaFamilySyntax

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

namespace IntegrationInACVF.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- An actual finite-arity RV-valued function, with its complete graph
definable over the unchanged original Gamma base. -/
structure GammaRVMap (G : GammaParameters.Base (M := M)) {n m : ℕ}
    (A : Set (Point (M := M) n m)) (d : ℕ) where
  toFun : A → Fin d → RV (M := M)
  graph : GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) 0 d) =>
    ∃ a : A, a.val = p ∧ toFun a = q.2)

namespace GammaRVMap

variable {G : GammaParameters.Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

theorem domain_definable (P : GammaRVMap G A d) : GammaSetDefinable G A := by
  have h := (gammaLogicInput G).image_graph ((gammaLogicInput G).swap_graph P.graph)
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨(Fin.elim0,P.toFun ⟨p,hp⟩),⟨p,hp⟩,rfl,rfl⟩
  · rintro ⟨q,a,ha,_⟩
    exact ha ▸ a.property

def restrict (P : GammaRVMap G A d) (D : Set (Point (M := M) n m))
    (hDA : D ⊆ A) (hD : GammaSetDefinable G D) : GammaRVMap G D d where
  toFun a := P.toFun ⟨a.val,hDA a.property⟩
  graph := by
    have h := (gammaLogicInput G).restrict_graph hD P.graph
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨hp,a,ha,he⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      have haa : (⟨p,hDA hp⟩ : A) = a := Subtype.ext ha.symm
      exact haa ▸ he
    · rintro ⟨a,ha,he⟩
      exact ⟨ha ▸ a.property,⟨a.val,hDA a.property⟩,ha,he⟩

def fromRefinement {m d : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e) :
    GammaRVMap G (GammaFamilySyntax.domain A) d where
  toFun a i := ⟨e (GammaFamilySyntax.labels a.val) (vfAt a.val 0).val i,
    he.1 _ _ a.property i⟩
  graph := by
    let ι := Fin ((1+m)+(0+d))
    let key (i : Fin m) : ι := Fin.castAdd (0+d) (Fin.natAdd 1 i)
    let x : ι := Fin.castAdd (0+d) (Fin.castAdd m (0 : Fin 1))
    let out (i : Fin d) : ι := Fin.natAdd (1+m) (Fin.natAdd 0 i)
    let ρ : (Fin m ⊕ Fin 1) ⊕ Fin d → ι :=
      Sum.elim (Sum.elim key (fun _ => x)) out
    have h := GammaTupleGraphs.relation_of_full G _ (FullBaseAtomicity.OverBase.preimage_comp he.2 ρ)
    apply GammaGraphDefinable.congr h
    intro p q
    change ((Fin.append (gammaPointCode p) (gammaPointCode q) x) ∈
      A (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)) ∧
      (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (out i)) =
        e (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i))
          (Fin.append (gammaPointCode p) (gammaPointCode q) x)) ↔ _
    simp only [key,x,out,Fin.append_left,Fin.append_right,gammaPointCode]
    constructor
    · rintro ⟨hp,hq⟩
      refine ⟨⟨p,hp⟩,rfl,funext fun i => ?_⟩
      exact Subtype.ext (congrFun hq i).symm
    · rintro ⟨a,rfl,hq⟩
      refine ⟨a.property,funext fun i => ?_⟩
      exact (congrArg Subtype.val (congrFun hq i)).symm

def keyPointMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace 0 (n+m)) S) :=
  Map.comp (flattenKeyMap (PresentedSet.univ (keySpace n m) S))
    (keyMap (PresentedSet.univ (pointSpace n m) S))

def fromSpecial {m l : ℕ} {A : Set (Point (M := M) 1 m)} {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G A E) : GammaRVMap G A (1+l) where
  toFun a := (keyPointMap G.real 1 l
    ⟨(T.special.toMap ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mpr a.property⟩).val,Set.mem_univ _⟩).val.2
  graph := by
    let hΓ := gammaLogicInput G
    have h := hΓ.comp_graph (GammaChainDefinable.graph hΓ T.special.chain T.invariant_graphs)
      (hΓ.real_map_graph (keyPointMap G.real 1 l))
    apply GammaGraphDefinable.congr h
    intro p q
    constructor
    · rintro ⟨z,⟨a,ha,hz⟩,⟨u,hu,hq⟩⟩
      refine ⟨⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mp a.property⟩,ha,?_⟩
      have huu : u = ⟨(T.special.toMap a).val,Set.mem_univ _⟩ := Subtype.ext (hu.trans hz.symm)
      rw [huu] at hq
      exact congrArg Prod.snd hq
    · rintro ⟨a,ha,hq⟩
      let b : T.source := ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mpr a.property⟩
      refine ⟨(T.special.toMap b).val,⟨b,ha,rfl⟩,
        ⟨⟨(T.special.toMap b).val,Set.mem_univ _⟩,rfl,?_⟩⟩
      exact Prod.ext (Subsingleton.elim _ _) hq

end GammaRVMap
end IntegrationInACVF.Section4
