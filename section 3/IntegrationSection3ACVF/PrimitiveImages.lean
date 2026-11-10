import IntegrationSection3ACVF.PrimitiveDecomposition
import IntegrationSection3ACVF.PuncturedImageComponents

/-! Lemma 3.8 with a genuine primitive component,
partial-domain definable graph, and the unchanged interpreted base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.PrimitiveImages

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def OnePrimitiveComponent (A : Set M) : Prop :=
  ∃ d : PuncturedBall M, A = d.body ∧
    ∃ k : PaperBalls.PrimitiveKind, PaperBalls.HasPrimitiveKind d k

theorem atomic_image (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    AdjoinBall.AtomicOver B (f '' A) := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ⟨ImaginaryBaseImages.image_definable hf,ImaginaryBaseImages.completeType_image hp hA.2 hf⟩

theorem lemma_3_8 (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A) (hOne : OnePrimitiveComponent A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    AdjoinBall.AtomicOver B (f '' A) ∧ OnePrimitiveComponent (f '' A) := by
  have hImage := atomic_image B hA f hf
  obtain ⟨d,hAd,_⟩ := hOne
  have hdAtomic : AdjoinBall.AtomicOver B d.body := hAd ▸ hA
  have hdf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f) := hAd ▸ hf
  have hdfVF : ∀ x ∈ d.body, iVF (f x) := hAd ▸ hfVF
  obtain ⟨F,j,hF,hSingle,hEq⟩ := PuncturedImageComponents.image_of_atomic_punctured
    B δ hδ1 d hdAtomic f hdf hdfVF
  have hAtomic : AdjoinBall.AtomicOver B (f '' d.body) := hAd ▸ hImage
  have hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧
        region F (BallImaginaries.underlying j) ⊆ f '' d.body := by
    have hm : j ∈ ({j} : Set (BallImaginaries.Ball M)) := rfl
    rw [← hSingle] at hm
    exact hm
  obtain ⟨k,hjk,_⟩ := PrimitiveDecomposition.common_kind B h00 δ hδ hδ1
    hAtomic.1 hAtomic.2 hF j j hj hj
  refine ⟨hImage,PrimitiveDecomposition.piece F (minimal_support_encoded hF) j,?_,k,hjk⟩
  rw [hAd,PrimitiveDecomposition.piece_body]
  exact hEq

end IntegrationInACVF.Section3ACVF.PrimitiveImages
