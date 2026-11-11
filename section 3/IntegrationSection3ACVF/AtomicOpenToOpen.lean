import IntegrationSection3ACVF.OpenSubballImages
import IntegrationSection3ACVF.RVInverse
import IntegrationSection3ACVF.MaximalOpenClasses

/-! Definable bijections between actual definable atomic VF sets have
the open-to-open property, using checked arbitrary-radius open subball
images in both directions. No unrestricted complete-type 3.15 is assumed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AtomicOpenToOpen

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem image_open (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (D : Set M) (hD : PaperBalls.IsOpenBall D) (hDA : D ⊆ A) : PaperBalls.IsOpenBall (f '' D) := by
  have hBall : IsBall D := by
    rcases hD with hv | ⟨a,α,rfl⟩
    · exact Or.inl hv
    · exact BallEnlargementGeometry.gammaBall_isBall a α true
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded D hBall
  have hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := hi.symm ▸ hD
  have hsub : BallImaginaries.underlying i ⊆ A := hi.symm ▸ hDA
  have ho := OpenSubballImages.image_open_of_atomic B h00 δ hδ hδ1 hA f hf hfVF hinj i hOpen hsub
  exact hi ▸ ho

theorem open_to_open (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : AdjoinBall.AtomicOver B A) (hC : AdjoinBall.AtomicOver B C)
    (hAVF : A ⊆ {x | iVF x}) (hCVF : C ⊆ {x | iVF x})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) : MaximalOpenClasses.OpenToOpen A f := by
  have hImage : f '' A = C := hbij.image_eq
  let g := RVInverse.inverse A f
  have hgGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn C g) := by
    have hg := RVInverse.inverse_graph_definable B hbij.2.1 hf
    rwa [hImage] at hg
  have hgVF (y : M) (hy : y ∈ C) : iVF (g y) :=
    hAVF (RVInverse.inverse_right ((Set.ext_iff.mp hImage y).mpr hy)).1
  have hgInj : Set.InjOn g C := hImage ▸ RVInverse.inverse_injOn A f
  intro D hDA
  constructor
  · intro ho
    exact image_open B h00 δ hδ hδ1 hA f hf (fun x hx => hCVF (hbij.1 hx)) hbij.2.1 D ho hDA
  · intro ho
    have hDC : f '' D ⊆ C := by
      rintro y ⟨x,hx,rfl⟩
      exact hbij.1 (hDA hx)
    have hBack := image_open B h00 δ hδ hδ1 hC g hgGraph hgVF hgInj (f '' D) ho hDC
    have hEq : g '' (f '' D) = D := by
      apply Set.Subset.antisymm
      · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
        have he : g (f z) = z := RVInverse.inverse_on hbij.2.1 (hDA hz)
        exact Eq.mpr (congrArg (fun w : M => w ∈ D) he) hz
      · intro x hx
        exact ⟨f x,⟨x,hx,rfl⟩,RVInverse.inverse_on hbij.2.1 (hDA hx)⟩
    exact hEq ▸ hBack

end IntegrationInACVF.Section3ACVF.AtomicOpenToOpen
