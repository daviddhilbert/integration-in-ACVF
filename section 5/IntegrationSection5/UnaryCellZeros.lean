import IntegrationSection5.UnaryPaperBallBridge
import ValuedFieldExtension

/-! A mutually contractible unary bijection between actual RV-pullbacks preserves zero and nonzero VF coordinates. A nonzero RV cell has at least two points by the nontrivial valuation axiom. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m l : ℕ} {S : Set M}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem nonzero_rv_cell_another (a : Point (M := M) 1 m) (ha : vfAt a 0 ≠ 0) :
    ∃ b : Point (M := M) 1 m, SameRV b a ∧ vfAt b 0 ≠ vfAt a 0 := by
  obtain ⟨ε,hε0,hε⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hεv : v ε < 1 := by
    have h := (not_congr (hv 1 ε)).mp hε
    simpa only [map_one] using lt_of_not_ge h
  let x := vfAt a 0
  let y := x + x*ε
  have hxy : y ≠ x := by
    intro he
    have he' : x + x*ε = x+0 := he.trans (add_zero x).symm
    exact mul_ne_zero ha hε0 (add_left_cancel he')
  have hclose : v (y-x) < v x := by
    change v (x+x*ε-x) < v x
    rw [add_sub_cancel_left,map_mul]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hεv (zero_lt_iff.mpr ((v.ne_zero_iff).mpr ha))
  have hrv : rv y = rv x := Subtype.ext (Balls.rv_eq_of_sub_lt v hv y x ha hclose)
  refine ⟨unaryInsert a.2 y,?_,hxy⟩
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,rfl⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hrv

theorem unary_bijection_maps_zero (f : Map A B) (hf : Function.Bijective f)
    (hback : Contractible (Map.inverse f hf)) (hB : IsRVPullback (carrier B))
    (a : A) (ha : vfAt a.val 0 = 0) : vfAt (f a).val 0 = 0 := by
  by_contra hn
  obtain ⟨q,hq,hne⟩ := nonzero_rv_cell_another (f a).val hn
  let b : B := ⟨q,(isRVPullback_iff _).mp hB (f a).val (f a).property q hq.symm⟩
  have he := hback (f a) b hq.symm
  rw [Map.inverse_apply] at he
  have hab : a = Map.inverse f hf b := Subtype.ext (eq_of_sameRV_of_zero he ha)
  have hfb : f a = b := by rw [hab,Map.apply_inverse]
  exact hne (congrArg (fun c : B => vfAt c.val 0) hfb).symm

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m l : ℕ} {S : Set M}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_bijection_zero_iff (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B)) (a : A) :
    vfAt (f a).val 0 = 0 ↔ vfAt a.val 0 = 0 := by
  constructor
  · intro hz
    by_contra hn
    obtain ⟨q,hq,hne⟩ := nonzero_rv_cell_another a.val hn
    let b : A := ⟨q,(isRVPullback_iff _).mp hA a.val a.property q hq.symm⟩
    have he := hc a b hq.symm
    have hab : a = b := hf.1 (Subtype.ext (eq_of_sameRV_of_zero he hz))
    exact hne (congrArg (fun c : A => vfAt c.val 0) hab).symm
  · exact unary_bijection_maps_zero f hf hback hB a

end IntegrationInACVF.Section5
