import IntegrationSection3ACVF.OrdinarySeparation
import IntegrationSection3ACVF.OpenBallConstancy

/-! Packaging of corrected Lemma 3.11 in the sequel's ball
conventions. Nonemptiness of the relation is the author-approved correction.
No centre or radius is required to be named in the original base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.Separation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def unpunctured (b : VFType (M := M)) (α : Values.Gamma (M := M)) : PuncturedBall M where
  parent := gammaBall b α false
  parent_ball := BallEnlargementGeometry.gammaBall_isBall b α false
  holes := ∅
  holes_ball := by simp
  holes_proper := by simp
  holes_disjoint := by simp

theorem unpunctured_body (b : VFType (M := M)) (α : Values.Gamma (M := M)) :
    (unpunctured b α).body = gammaBall b α false := by
  ext x
  simp [PuncturedBall.body,unpunctured]

theorem for_punctured_target (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {O : Set M} (hOpen : PaperBalls.IsOpenBall O) (hO : AdjoinBall.AtomicOver B O)
    (d : PuncturedBall M) (hd : AdjoinBall.AtomicOver B d.body)
    (b : VFType (M := M)) (α : Values.Gamma (M := M))
    (hParent : d.parent = gammaBall b α false)
    (hholes : ∀ h ∈ d.holes, ∃ a : VFType (M := M), h = gammaBall a α true)
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hRsub : R ⊆ O ×ˢ d.body) (hne : R.Nonempty) :
    ¬ (∀ x ∈ O, {y | (x,y) ∈ R}.Finite) := by
  rcases hOpen with hVF | ⟨c,σ,hOeq⟩
  · exact (OpenBallConstancy.atomic_not_contains_vf B hO (hVF.symm ▸ Set.Subset.rfl)).elim
  · obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded c σ
    have hiO : BallImaginaries.underlying i = O := hi.trans hOeq.symm
    have hiAtomic : AdjoinBall.AtomicOver B (BallImaginaries.underlying i) := by
      simpa only [hiO] using hO
    have hsub : R ⊆ BallImaginaries.underlying i ×ˢ d.body := by
      simpa only [hiO] using hRsub
    have hnot := OrdinarySeparation.not_finite_rows_unnamed_radius B h00 δ hδ hδ1
      i hiAtomic c σ hi d hd b α hParent hholes hR hsub hne
    simpa only [hiO] using hnot

theorem lemma_3_11 (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {O L : Set M} (hOpen : PaperBalls.IsOpenBall O)
    (hO : AdjoinBall.AtomicOver B O) (hL : AdjoinBall.AtomicOver B L)
    (hTarget : (PaperBalls.IsClosedBall L ∧
      ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius L r ∧
        r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
      ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = L)
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hRsub : R ⊆ O ×ˢ L) (hne : R.Nonempty) :
    ¬ (∀ x ∈ O, {y | (x,y) ∈ R}.Finite) := by
  rcases hTarget with ⟨hClosed,r,hr,hlt⟩ | ⟨d,hThin,hbody⟩
  · rcases hClosed with hVF | ⟨a,ha⟩ | ⟨b,α,hLeq⟩
    · exact (OpenBallConstancy.atomic_not_contains_vf B hL (hVF.symm ▸ Set.Subset.rfl)).elim
    · have hp : PaperBalls.HasRadius L
          (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M)) :=
        Or.inr (Or.inl ⟨a,ha,rfl⟩)
      have he := PaperBallInvariants.hasRadius_unique δ hδ1 hr hp
      exact (not_lt_of_ge he.ge hlt).elim
    · let d := unpunctured b α
      have he : d.body = L := (unpunctured_body b α).trans hLeq.symm
      have hd : AdjoinBall.AtomicOver B d.body := by simpa only [he] using hL
      have hsub : R ⊆ O ×ˢ d.body := by simpa only [he] using hRsub
      exact for_punctured_target B h00 δ hδ hδ1 hOpen hO d hd b α rfl
        (by simp [d,unpunctured]) hR hsub hne
  · obtain ⟨b,a,α,hParent,hholes⟩ := hThin
    have hd : AdjoinBall.AtomicOver B d.body := by simpa only [hbody] using hL
    have hsub : R ⊆ O ×ˢ d.body := by simpa only [hbody] using hRsub
    apply for_punctured_target B h00 δ hδ hδ1 hOpen hO d hd b α hParent _ hR hsub hne
    intro h hh
    rw [hholes] at hh
    exact ⟨a,Finset.mem_singleton.mp hh⟩

end IntegrationInACVF.Section3ACVF.Separation
