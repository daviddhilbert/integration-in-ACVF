import IntegrationSection3ACVF.PrimitiveImages
import IntegrationSection3ACVF.SeparationFunctions

/-! Lemma 3.13, connecting primitive image classification with the
actual separation theorem. Its classification and separation prerequisites are proved in the imported modules. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OpenImages

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_one_component {A : Set M} (hOpen : PaperBalls.IsOpenBall A) :
    PrimitiveImages.OnePrimitiveComponent A := by
  have hBall : IsBall A := by
    rcases hOpen with he | ⟨a,α,he⟩
    · exact Or.inl he
    · rw [he]
      exact BallEnlargementGeometry.gammaBall_isBall a α true
  let d : PuncturedBall M := {
    parent := A
    parent_ball := hBall
    holes := ∅
    holes_ball := by simp
    holes_proper := by simp
    holes_disjoint := by simp }
  have he : d.body = A := by
    ext x
    simp [PuncturedBall.body,d]
  exact ⟨d,he.symm,.openBall,rfl,hOpen⟩

theorem body_eq_parent {d : PuncturedBall M} (h : d.holes = ∅) : d.body = d.parent := by
  ext x
  simp [PuncturedBall.body,h]

theorem lemma_3_13 (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hOpen : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    (∃ c : VFType (M := M), ∀ x ∈ A, f x = c.val) ∨
      (AdjoinBall.AtomicOver B (f '' A) ∧ PaperBalls.IsOpenBall (f '' A)) := by
  obtain ⟨hImage,one⟩ := PrimitiveImages.lemma_3_8 B h00 δ hδ hδ1 hA
    (open_one_component hOpen) f hf hfVF
  obtain ⟨d,he,k,hk⟩ := one
  have hfImage (x : M) (hx : x ∈ A) : f x ∈ f '' A := ⟨x,hx,rfl⟩
  cases k with
  | openBall =>
    refine Or.inr ⟨hImage,?_⟩
    rw [he,body_eq_parent hk.1]
    exact hk.2
  | closedBall =>
    have hbody := body_eq_parent hk.1
    rcases hk.2 with hVF | ⟨a,ha⟩ | ⟨b,α,hb⟩
    · exact Or.inr ⟨hImage,Or.inl (he.trans (hbody.trans hVF))⟩
    · refine Or.inl ⟨a,?_⟩
      intro x hx
      have hm := hfImage x hx
      rwa [he,hbody,ha] at hm
    · have hγinf : α.val < Values.infinity :=
        lt_of_le_of_ne (Values.le_infinity α.val) α.property
      have hp : f '' A = gammaBall b α false := he.trans (hbody.trans hb)
      have ht : (PaperBalls.IsClosedBall (f '' A) ∧
          ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius (f '' A) r ∧
            r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
          ∃ e : PuncturedBall M, PaperBalls.IsThinAnnulus e ∧ e.body = f '' A :=
        Or.inl ⟨Or.inr (Or.inr ⟨b,α,hp⟩),↑α.val,
          Or.inr (Or.inr ⟨b,α,false,hp,rfl⟩),WithBot.coe_lt_coe.mpr hγinf⟩
      exact (SeparationFunctions.no_function_from_open B h00 δ hδ hδ1 hOpen hA hImage ht
        f hf hfImage).elim
  | thinAnnulus =>
    have ht : (PaperBalls.IsClosedBall (f '' A) ∧
        ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius (f '' A) r ∧
          r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
        ∃ e : PuncturedBall M, PaperBalls.IsThinAnnulus e ∧ e.body = f '' A :=
      Or.inr ⟨d,hk,he.symm⟩
    exact (SeparationFunctions.no_function_from_open B h00 δ hδ hδ1 hOpen hA hImage ht
      f hf hfImage).elim

end IntegrationInACVF.Section3ACVF.OpenImages
