import IntegrationSection3ACVF.OpenImages
import IntegrationSection3.PartialInverse

/-! Definable partial inverses over the full original base, and the
atomic open image of an injective map on an atomic open ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVInverse

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def inverse (A : Set M) (f : M → M) : M → M :=
  @Function.invFunOn M M ⟨iVFZero⟩ f A

theorem inverse_on {A : Set M} {f : M → M} (hinj : Set.InjOn f A)
    {x : M} (hx : x ∈ A) : inverse A f (f x) = x := by
  letI : Nonempty M := ⟨iVFZero⟩
  exact hinj.leftInvOn_invFunOn hx

theorem inverse_right {A : Set M} {f : M → M} {y : M} (hy : y ∈ f '' A) :
    inverse A f y ∈ A ∧ f (inverse A f y) = y := by
  letI : Nonempty M := ⟨iVFZero⟩
  exact Function.invFunOn_pos hy

theorem inverse_injOn (A : Set M) (f : M → M) : Set.InjOn (inverse A f) (f '' A) := by
  intro x hx y hy he
  exact (inverse_right hx).2.symm.trans ((congrArg f he).trans (inverse_right hy).2)

theorem inverse_graph_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} {f : M → M} (hinj : Set.InjOn f A)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (f '' A) (inverse A f)) := by
  letI : Nonempty M := ⟨iVFZero⟩
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact PartialInverse.graph_definable hinj hf

theorem atomic_open_image (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A) :
    AdjoinBall.AtomicOver B (f '' A) ∧ PaperBalls.IsOpenBall (f '' A) := by
  rcases OpenImages.lemma_3_13 B h00 δ hδ hδ1 ho hA f hf hfVF with hc | hi
  · obtain ⟨c,hc⟩ := hc
    have hsingle : A.Subsingleton := by
      intro x hx y hy
      exact hinj hx hy ((hc x hx).trans (hc y hy).symm)
    exact ((SeparationFunctions.open_infinite h00 δ hδ1 ho) hsingle.finite).elim
  · exact hi

end IntegrationInACVF.Section3ACVF.RVInverse
