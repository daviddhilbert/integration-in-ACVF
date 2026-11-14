import Section3.GammaBaseTools
import Section9.SpecialJacobianGeneric

/-! A uniform first-order operation on sets descends to the original
imaginary Gamma parameters. Its real formula keeps the representative code
free, and equality of code rows gives the required representative invariance. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section8

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_definable_transform
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {a b : ℕ}
    (sa : Fin a → SortTag) (sb : Fin b → SortTag)
    (F : Set (Fin a → M) → Set (Fin b → M))
    (hUniform : ∀ (p : ℕ) (R : Set (Fin p ⊕ Fin a → M)), B.real.Definable LRV R →
      B.real.Definable LRV {w : Fin p ⊕ Fin b → M |
        w ∘ Sum.inr ∈ F {x | Sum.elim (w ∘ Sum.inl) x ∈ R}})
    (hProper : ∀ C : Set (Fin a → M), (∀ x ∈ C, ∀ i, sortEval (sa i) (x i)) →
      ∀ y ∈ F C, ∀ i, sortEval (sb i) (y i))
    {A : Set (Fin a → M)} (hA : DefinableOverBase B sa A) :
    DefinableOverBase B sb (F A) := by
  obtain ⟨g,γ,hγ,R,hRA⟩ := hA
  let C : Set (Fin g ⊕ Fin a → M) := {w | (w ∘ Sum.inl,w ∘ Sum.inr) ∈ R.carrier}
  have hC : B.real.Definable LRV C :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M (@Base.real M sM hM B) LRV I (Fin g ⊕ Fin a) C)
      (normalize_eq_of_isCanonical hc)) R.definable
  let D : Set (Fin g ⊕ Fin b → M) := {w | w ∘ Sum.inr ∈
    F {x | (w ∘ Sum.inl,x) ∈ R.carrier}}
  have hD : B.real.Definable LRV D := hUniform g C hC
  have hDN : @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin g ⊕ Fin b) D :=
    Eq.mp (congrArg (fun I : LRV.Structure M => @Set.Definable M (@Base.real M sM hM B) LRV I (Fin g ⊕ Fin b) D)
      (normalize_eq_of_isCanonical hc).symm) hD
  let Q : Relation B.real g b sb := {
    carrier := {p | Proper p.1 ∧ p.2 ∈ F {x | (p.1,x) ∈ R.carrier}}
    definable := by
      have hp := proper_normalized_definable (M := M) B.real (n := g)
      let N := @CanonicalStructure.normalize M sM
      letI := N
      exact (hp.preimage_comp Sum.inl).inter hDN
    proper := by
      intro p hp
      exact ⟨hp.1,hProper _ (fun x hx => (R.proper _ hx).2) p.2 hp.2⟩
    invariant := by
      intro t u htu y
      have he : {x | (rawTuple t,x) ∈ R.carrier} = {x | (rawTuple u,x) ∈ R.carrier} :=
        Set.ext (R.invariant t u htu)
      change (Proper (rawTuple t) ∧ y ∈ F _) ↔ (Proper (rawTuple u) ∧ y ∈ F _)
      rw [he]
      simp only [rawTuple_proper,true_and] }
  refine ⟨g,γ,hγ,Q,?_⟩
  have hrow : {x | (rawTuple (representatives γ),x) ∈ R.carrier} = A := hRA
  ext y
  change (Proper (rawTuple (representatives γ)) ∧ y ∈ F _) ↔ y ∈ F A
  rw [hrow,and_iff_right (rawTuple_proper (representatives γ))]

end IntegrationInACVF.Section7
