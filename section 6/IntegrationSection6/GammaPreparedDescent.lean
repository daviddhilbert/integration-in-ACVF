import IntegrationSection6.GammaPreparedFamilies
import Section5.GammaRestriction

/-! Full Gamma families that are constant on prepared RV-polydiscs descend
to actual RV-key-indexed families. The descended graph retains the original
Gamma base and agrees with every representative of each prepared key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m l a : ℕ}

def fullRVKeyMap (S : Set M) (n m : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace (M := M) 0 (n+m)) S) :=
  @Map.comp M sM _ _ _ S _ _ _
    (flattenKeyMap (PresentedSet.univ (keySpace (M := M) n m) S))
    (keyMap (PresentedSet.univ (pointSpace (M := M) n m) S))

theorem fullRVKeyMap_value (S : Set M) (n m : ℕ)
    (p : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (fullRVKeyMap S n m p).val = flatKey p.val := rfl

def rvDescendedRelation (C : DefSet (M := M) S n m)
    (r : C → Point (M := M) 0 a → Prop)
    (t : Point (M := M) 0 (n+m)) (z : Point (M := M) 0 a) : Prop :=
  ∃ x : C, flatKey x.val = t ∧ r x z

theorem gamma_rv_descended_graph (C : DefSet (M := M) S n m)
    (r : C → Point (M := M) 0 a → Prop)
    (hr : GammaGraphDefinable B (fun (p : Point (M := M) n m) z => ∃ x : C, x.val = p ∧ r x z)) :
    GammaGraphDefinable B (rvDescendedRelation C r) := by
  let L := gammaLogicInput B
  have hK := L.real_map_graph (fullRVKeyMap B.real n m)
  have h := L.comp_graph (L.swap_graph hK) hr
  apply GammaGraphDefinable.congr h
  intro t z
  constructor
  · rintro ⟨p,⟨y,hy,ht⟩,⟨x,hx,hxz⟩⟩
    refine ⟨x,?_,hxz⟩
    have he : y.val = x.val := hy.trans hx.symm
    exact (congrArg flatKey he).symm.trans ht
  · rintro ⟨x,hxt,hxz⟩
    exact ⟨x.val,⟨⟨x.val,Set.mem_univ _⟩,rfl,hxt⟩,x,rfl,hxz⟩

theorem rvDescendedRelation_spec (C : DefSet (M := M) S n m)
    (r : C → Point (M := M) 0 a → Prop)
    (hrows : ∀ x y : C, SameRV x.val y.val → ∀ z, r x z ↔ r y z)
    (x : C) (z : Point (M := M) 0 a) :
    rvDescendedRelation C r (flatKey x.val) z ↔ r x z := by
  constructor
  · rintro ⟨y,hy,hr⟩
    exact (hrows y x ((flatKey_eq_iff _ _).mp hy) z).mp hr
  · exact fun hr => ⟨x,rfl,hr⟩

theorem gamma_prepared_rv_descent
    {A : DefSet (M := M) S n 0} {C : DefSet (M := M) S n l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (r : Point (M := M) n 0 → Point (M := M) 0 a → Prop)
    (hr : GammaGraphDefinable B r) :
    GammaGraphDefinable B (rvDescendedRelation C (fun x z => r (T.inverseMap x).val z)) := by
  have hi := gamma_inverse_graph (gammaLogicInput B) T hT
  have h := (gammaLogicInput B).comp_graph hi hr
  apply gamma_rv_descended_graph C _
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨y,⟨x,hx,hy⟩,hr⟩
    exact ⟨x,hx,hy.symm ▸ hr⟩
  · rintro ⟨x,hx,hr⟩
    exact ⟨(T.inverseMap x).val,⟨x,hx,rfl⟩,hr⟩

end IntegrationInACVF.Section6
