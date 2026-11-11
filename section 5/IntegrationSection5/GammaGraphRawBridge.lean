import IntegrationSection5.GammaPointRawBridge
import IntegrationSection5.UnaryCoordinateGeometry
import IntegrationSection3.FiniteTupleGraphs

/-! The complete graph of the actual unary mixed map, as a raw finite tuple
graph for Proposition3.21. The chosen totalization is used only on its domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {n m u w : ℕ}

def pointRelationIndex (n m u w : ℕ) :
    ((Fin n ⊕ Fin m) ⊕ (Fin u ⊕ Fin w)) ≃ Fin ((n+m)+(u+w)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

theorem pointRelationValues_eq_code (p : Point (M := M) n m) (q : Point (M := M) u w) :
    Sum.elim (pointValues p) (pointValues q) =
      Fin.append (gammaPointCode p) (gammaPointCode q) ∘ pointRelationIndex n m u w := by
  funext i
  cases i with
  | inl i =>
    change pointValues p i = _
    simp only [pointRelationIndex,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      finSumFinEquiv_apply_left,Fin.append_left,Function.comp_apply]
    exact congrFun (pointValues_eq_gammaPointCode p) i
  | inr i =>
    change pointValues q i = _
    simp only [pointRelationIndex,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      finSumFinEquiv_apply_right,Fin.append_right,Function.comp_apply]
    exact congrFun (pointValues_eq_gammaPointCode q) i

theorem gammaGraph_full_raw
    (r : Point (M := M) n m → Point (M := M) u w → Prop) (hr : GammaGraphDefinable P r) :
    FullBaseAtomicity.OverBase (sM := sM) (gammaFullBase P)
      {z | ∃ p q, r p q ∧ Sum.elim (pointValues p) (pointValues q) = z} := by
  let e := pointRelationIndex n m u w
  have h := FullBaseAtomicity.OverBase.preimage_comp (gamma_to_full hr) e.symm
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  constructor
  · rintro ⟨p,q,hpq,he⟩
    refine ⟨p,q,hpq,?_⟩
    rw [pointRelationValues_eq_code,he]
    funext i
    exact congrArg z (e.symm_apply_apply i)
  · rintro ⟨p,q,hpq,rfl⟩
    refine ⟨p,q,hpq,?_⟩
    rw [pointRelationValues_eq_code]
    funext i
    exact congrArg (Fin.append (gammaPointCode p) (gammaPointCode q)) (e.apply_symm_apply i).symm

theorem unaryTupleMap_graph {m l : ℕ} {A : DefSet (M := M) S 1 m}
    {B : DefSet (M := M) S 1 l} (f : Map A B)
    (hf : GammaGraphDefinable P (pointMapGraph f)) :
    FullBaseAtomicity.OverBase (sM := sM) (gammaFullBase P)
      (FiniteTupleGraphs.graph (pointValues '' carrier A) (unaryTupleMap f)) := by
  apply FullBaseAtomicity.OverBase.congr (gammaGraph_full_raw (pointMapGraph f) hf)
  intro z
  constructor
  · rintro ⟨p,q,⟨a,rfl,hq⟩,he⟩
    have hleft : pointValues a.val = z ∘ Sum.inl := congrArg (fun x => x ∘ Sum.inl) he
    have hright : pointValues q = z ∘ Sum.inr := congrArg (fun x => x ∘ Sum.inr) he
    refine ⟨⟨a.val,a.property,hleft⟩,?_⟩
    rw [← hleft,unaryTupleMap_apply,hq]
    exact hright.symm
  · rintro ⟨⟨p,hp,hpcode⟩,hout⟩
    let a : A := ⟨p,hp⟩
    refine ⟨p,(f a).val,⟨a,rfl,rfl⟩,?_⟩
    have he : pointValues (f a).val = z ∘ Sum.inr := by
      rw [← hpcode,unaryTupleMap_apply f a] at hout
      exact hout.symm
    funext i
    cases i with
    | inl i => exact congrFun hpcode i
    | inr i => exact congrFun he i

theorem unaryTupleMap_injective {m l : ℕ} {A : DefSet (M := M) S 1 m}
    {B : DefSet (M := M) S 1 l} (f : Map A B) (hf : Function.Injective f) :
    Set.InjOn (unaryTupleMap f) (pointValues '' carrier A) := by
  rintro x ⟨p,hp,rfl⟩ y ⟨q,hq,rfl⟩ he
  let a : A := ⟨p,hp⟩
  let b : A := ⟨q,hq⟩
  rw [unaryTupleMap_apply f a,unaryTupleMap_apply f b] at he
  have hab : a = b := hf (Subtype.ext (pointValues_injective he))
  exact congrArg (fun c : A => pointValues c.val) hab

end IntegrationInACVF.Section5
