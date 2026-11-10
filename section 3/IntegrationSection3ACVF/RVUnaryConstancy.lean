import IntegrationSection3ACVF.OpenBallConstancy

/-! The unary RV-valued consequence of Lemma 3.9 for a partial-domain graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVUnaryConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def family (g : M → M) (x : VFType (M := M)) : Set (Fin 1 → M) := {ys | ys 0 = g x.val}

theorem graph_eq {A : Set M} (hAVF : A ⊆ {x | iVF x}) (g : M → M) :
    ImaginaryBaseImages.graphOn A g = OpenBallConstancy.graphOn A (family g) := by
  ext z
  change (z 0 ∈ A ∧ z 1 = g (z 0)) ↔
    (∃ x : VFType (M := M), x.val = z 0 ∧ z 1 = g x.val) ∧ z 0 ∈ A
  exact ⟨fun ⟨ha,he⟩ => ⟨⟨⟨z 0,hAVF ha⟩,rfl,he⟩,ha⟩,
    fun ⟨⟨x,hx,he⟩,ha⟩ => ⟨ha,hx ▸ he⟩⟩

theorem constant (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (g : M → M) (hg : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A g))
    (hgRV : ∀ x ∈ A, iRV (g x)) : ∀ x ∈ A, ∀ y ∈ A, g x = g y := by
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with he | ⟨a,α,he⟩
    · exact he ▸ Set.Subset.rfl
    · rw [he]
      exact fun _ hx => hx.1
  have hg' := hg
  rw [graph_eq hAVF g] at hg'
  have hSorted (x : VFType (M := M)) (hx : x.val ∈ A) (ys : Fin 1 → M)
      (hys : ys ∈ family g x) : ∀ j, iRV (ys j) := by
    intro j
    fin_cases j
    change iRV (ys 0)
    rw [show ys 0 = g x.val from hys]
    exact hgRV x.val hx
  have hc := OpenBallConstancy.lemma_3_9_open h00 B δ hδ hδ1 ho hA (family g) hSorted hg'
  intro x hx y hy
  have he := hc (⟨x,hAVF hx⟩ : VFType (M := M)) hx ⟨y,hAVF hy⟩ hy
  have hm : (![g x] : Fin 1 → M) ∈ family g (⟨x,hAVF hx⟩ : VFType (M := M)) := rfl
  exact (he ▸ hm : (![g x] : Fin 1 → M) ∈ family g (⟨y,hAVF hy⟩ : VFType (M := M)))

end IntegrationInACVF.Section3ACVF.RVUnaryConstancy
