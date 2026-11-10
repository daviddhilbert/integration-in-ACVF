import IntegrationSection3ACVF.RVDifferencePairs

/-! The RV graph of differences under a definable map on an atomic
open ball is independent of its chosen source point, by Lemma 3.9. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace IntegrationInACVF.Section3ACVF.RVPairConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def family (A : Set M) (f : M → M) (x : VFType (M := M)) : Set (Fin 2 → M) :=
  PairMapFibres.family A f (difference (M := M)) x.val

theorem graph_eq {A : Set M} (hAVF : A ⊆ {x | iVF x}) (f : M → M) :
    PairMapFibres.graph A f (difference (M := M)) = OpenBallConstancy.graphOn A (family A f) := by
  ext z
  change (z 0 ∈ A ∧ ∃ y ∈ A, z 1 = difference y (z 0) ∧
      z 2 = difference (f y) (f (z 0))) ↔
    (∃ x : VFType (M := M), x.val = z 0 ∧ ∃ y ∈ A,
      z 1 = difference y x.val ∧ z 2 = difference (f y) (f x.val)) ∧ z 0 ∈ A
  constructor
  · rintro ⟨ha,y,hy,ht,hs⟩
    exact ⟨⟨⟨z 0,hAVF ha⟩,rfl,y,hy,ht,hs⟩,ha⟩
  · rintro ⟨⟨x,hx,y,hy,ht,hs⟩,ha⟩
    exact ⟨ha,y,hy,by simpa only [hx] using ht,by simpa only [hx] using hs⟩

theorem family_rv {A : Set M} (hAVF : A ⊆ {x | iVF x})
    (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (x : VFType (M := M)) (hx : x.val ∈ A) (t : Fin 2 → M)
    (ht : t ∈ family A f x) : ∀ j, iRV (t j) := by
  obtain ⟨y,hy,ht,hs⟩ := ht
  have hd (a b : M) (ha : iVF a) (hb : iVF b) : iRV (difference a b) := by
    rw [difference_vf (⟨a,ha⟩ : VFType (M := M)) ⟨b,hb⟩]
    rw [sub_eq_add_neg]
    change iRV (iRv (iVFAdd a (iVFNeg b)))
    exact rv_mem hM (vf_add_mem hM ha (vf_neg_mem hM hb))
  intro j
  fin_cases j
  · change iRV (t 0)
    rw [ht]
    exact hd y x.val (hAVF hy) x.property
  · change iRV (t 1)
    rw [hs]
    exact hd (f y) (f x.val) (hfVF y hy) (hfVF x.val hx)

theorem constant (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    ∀ x : VFType (M := M), x.val ∈ A → ∀ y : VFType (M := M), y.val ∈ A →
      family A f x = family A f y := by
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with h | ⟨a,γ,h⟩
    · exact h ▸ Set.Subset.rfl
    · rw [h]
      intro x hx
      exact hx.1
  have hg := RVDifferencePairs.pair_graph_definable B hf
  rw [graph_eq hAVF f] at hg
  exact OpenBallConstancy.lemma_3_9_open h00 B δ hδ hδ1 ho hA (family A f)
    (family_rv hAVF f hfVF) hg

end IntegrationInACVF.Section3ACVF.RVPairConstancy
