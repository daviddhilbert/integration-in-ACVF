import IntegrationSection3ACVF.OpenImages
import IntegrationSection3ACVF.FullGammaRadius

/-! Open images of arbitrary-radius subballs of a definable atomic set.
The ambient-set definability is essential for this use of3.3; this theorem
is not the unrestricted complete-type statement of3.15. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.OpenSubballImages

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem image_open_of_atomic (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (i : BallImaginaries.Ball M) (hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hsub : BallImaginaries.underlying i ⊆ A) :
    PaperBalls.IsOpenBall (f '' BallImaginaries.underlying i) := by
  rcases hOpen with hVF | ⟨c,γ,hi⟩
  · exact (OpenBallConstancy.atomic_not_contains_vf B hA (hVF ▸ hsub)).elim
  · let Bγ := B.adjoin (Sum.inr γ)
    let C := Bγ.adjoin (Sum.inl i)
    let P := BallImaginaries.underlying (M := M) i
    have hAγ := FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hA γ
    have hγ : FullGammaSyntax.Scalar Bγ {γ} := AdjoinGamma.named_scalar γ (Set.mem_insert _ _)
    have hP := FullGammaRadius.lemma_3_4 Bγ γ hγ true hAγ.2 i c hi hsub
    have hδγ : FullGammaSyntax.Scalar Bγ {δ} :=
      FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
    have hδC : FullGammaSyntax.Scalar C {δ} :=
      FullBaseAtomicity.OverBase.mono hδγ Set.Subset.rfl (Set.subset_insert _ _)
    have hfγ : FullBaseAtomicity.OverBase Bγ (ImaginaryBaseImages.graphOn A f) :=
      FullBaseAtomicity.OverBase.mono hf Set.Subset.rfl (Set.subset_insert _ _)
    have hfC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn A f) :=
      FullBaseAtomicity.OverBase.mono hfγ Set.Subset.rfl (Set.subset_insert _ _)
    have hm := FullBaseAtomicity.OverBase.preimage_comp hP.1 (fun _ : Fin 1 => (0 : Fin 2))
    have hgraph : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn P f) := by
      apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hfC)
      intro z
      change (z 0 ∈ P ∧ z 0 ∈ A ∧ z 1 = f (z 0)) ↔ (z 0 ∈ P ∧ z 1 = f (z 0))
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
    have hOpenP : PaperBalls.IsOpenBall P := Or.inr ⟨c,γ,hi⟩
    rcases OpenImages.lemma_3_13 C h00 δ hδC hδ1 hOpenP hP f hgraph
        (fun x hx => hfVF x (hsub hx)) with hconstant | hopen
    · obtain ⟨a,ha⟩ := hconstant
      have hsingle : P.Subsingleton := by
        intro x hx y hy
        exact hinj (hsub hx) (hsub hy) ((ha x hx).trans (ha y hy).symm)
      exact ((SeparationFunctions.open_infinite h00 δ hδ1 hOpenP) hsingle.finite).elim
    · exact hopen.2

end IntegrationInACVF.Section3ACVF.OpenSubballImages
