import IntegrationSection4.GammaRelationPreparation

/-! Finite simultaneous original-base relation preparation. Every new
special-bijection chain is a genuine alternating refinement, and its inverse
preserves all previously prepared relations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.FiniteRelationPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b c d k : ℕ}
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
variable {C : DefSet (M := M) S n c} {D : DefSet (M := M) S n d}

def Uniform (r : Point (M := M) n a → Point (M := M) 0 k → Prop)
    (T : SpecialBijection A B) : Prop :=
  ∀ b c : B, SameRV b.val c.val → ∀ z, r (T.inverseMap b).val z ↔ r (T.inverseMap c).val z

def Refines (T : SpecialBijection A B) (U : SpecialBijection A C) : Prop :=
  ∀ b c : C, SameRV b.val c.val →
    SameRV (T.toMap (U.inverseMap b)).val (T.toMap (U.inverseMap c)).val

theorem refines_refl (T : SpecialBijection A B) : Refines T T := by
  intro b c he
  simpa only [T.apply_inverse] using he

theorem refines_comp (T : SpecialBijection A B) (U : SpecialBijection B C)
    (hAlt : (T.chain.append U.chain).Alternating none) : Refines T (T.comp U hAlt) := by
  intro b c he
  simpa only [SpecialBijection.comp_inverseMap,T.apply_inverse] using U.inverse_contractible b c he

theorem Refines.trans {T : SpecialBijection A B} {U : SpecialBijection A C}
    {V : SpecialBijection A D} (hTU : Refines T U) (hUV : Refines U V) : Refines T V := by
  intro b c he
  have hh := hTU (U.toMap (V.inverseMap b)) (U.toMap (V.inverseMap c)) (hUV b c he)
  simpa only [U.inverse_apply] using hh

theorem Uniform.refine {r : Point (M := M) n a → Point (M := M) 0 k → Prop}
    {T : SpecialBijection A B} {U : SpecialBijection A C}
    (h : Uniform r T) (hTU : Refines T U) : Uniform r U := by
  intro b c he z
  have hh := h (T.toMap (U.inverseMap b)) (T.toMap (U.inverseMap c)) (hTU b c he) z
  simpa only [T.inverse_apply] using hh

theorem prepare_finite {ι : Type} {κ : Cardinal}
    (hs : SpecialTransformations.Section3.Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : SpecialTransformations.Section3.GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : SpecialTransformations.Section3.GammaParameters.VFGammaGeneratedBase G)
    (hGS : G.real ⊆ S) (τ : SpecialBijection A B) (hτ : GammaChainDefinable G τ.chain)
    (hB : IsRVPullback (carrier B))
    (r : ι → Point (M := M) n a → Point (M := M) 0 k → Prop)
    (hr : ∀ i, GammaGraphDefinable G (r i)) (F : Finset ι) :
    ∃ l : ℕ, ∃ E : DefSet (M := M) S n l, ∃ T : SpecialBijection A E,
      GammaChainDefinable G T.chain ∧ IsRVPullback (carrier E) ∧
        Refines τ T ∧ ∀ i ∈ F, Uniform (r i) T := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨b,B,τ,hτ,hB,refines_refl τ,by simp⟩
  | @insert i F hi ih =>
    obtain ⟨l,E,T,hTG,hE,hRef,hPrepared⟩ := ih
    obtain ⟨q,D,U,hAlt,hUG,hD,hC⟩ := GammaRelationPreparation.prepare_after hs h00 G hsmall
      hGenerated hGS T hTG (r i) (hr i)
    let V := T.comp U hAlt
    have hVG : GammaChainDefinable G V.chain :=
      GammaRelationPreparation.chain_append_definable T.chain U.chain hTG hUG
    have hTV : Refines T V := refines_comp T U hAlt
    refine ⟨q,D,V,hVG,hD,hRef.trans hTV,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hC
    · exact (hPrepared j hj).refine hTV

end IntegrationInACVF.Section4.FiniteRelationPreparation
