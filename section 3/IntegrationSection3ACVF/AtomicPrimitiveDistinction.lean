import IntegrationSection3ACVF.AtomicOpenToOpen
import IntegrationSection3ACVF.ThinBallGeometry

/-! Proposition 3.23 for all ordered pairs of distinct actual primitive
shapes. The closed/thin-annulus case uses proved 3.22 and actual 0/1 hole
counts; the open cases use the checked separation theorem. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.AtomicPrimitiveDistinction

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def HasShape (k : PaperBalls.PrimitiveKind) (A : Set M) : Prop :=
  match k with
  | .openBall => PaperBalls.IsOpenBall A
  | .closedBall => PaperBalls.IsClosedBall A
  | .thinAnnulus => ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = A

theorem inverse_bijOn {A C : Set M} (f : M → M) (hbij : Set.BijOn f A C) :
    Set.BijOn (RVInverse.inverse A f) C A := by
  have hImage : f '' A = C := hbij.image_eq
  refine ⟨?_,hImage ▸ RVInverse.inverse_injOn A f,?_⟩
  · intro y hy
    exact (RVInverse.inverse_right ((Set.ext_iff.mp hImage y).mpr hy)).1
  · intro x hx
    exact ⟨f x,hbij.1 hx,RVInverse.inverse_on hbij.2.1 hx⟩

theorem no_open_target (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : AdjoinBall.AtomicOver B A) (hC : AdjoinBall.AtomicOver B C)
    (ho : PaperBalls.IsOpenBall A)
    (ht : PaperBalls.IsClosedBall C ∨ ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = C)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) : False := by
  let g := RVInverse.inverse A f
  have hImage : f '' A = C := hbij.image_eq
  have hgGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn C g) := by
    have hg := RVInverse.inverse_graph_definable B hbij.2.1 hf
    rwa [hImage] at hg
  have hgBij : Set.BijOn g C A := inverse_bijOn f hbij
  have hFin (x : M) (_ : x ∈ A) : {y | y ∈ C ∧ g y = x}.Finite := by
    have hs : ({y | y ∈ C ∧ g y = x} : Set M).Subsingleton := by
      intro y hy z hz
      exact hgBij.2.1 hy.1 hz.1 (hy.2.trans hz.2.symm)
    exact hs.finite
  exact SeparationFunctions.no_finite_to_one_to_open B h00 δ hδ hδ1 ho hA hC ht g hgGraph hgBij.1 hFin

theorem no_closed_thin (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : AdjoinBall.AtomicOver B A) (hC : AdjoinBall.AtomicOver B C)
    (hc : PaperBalls.IsClosedBall A)
    (ht : ∃ d : PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = C)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) : False := by
  classical
  obtain ⟨d,hd,hBody⟩ := ht
  have hD : AdjoinBall.AtomicOver B d.body := hBody.symm ▸ hC
  have hBijD : Set.BijOn f A d.body := hBody.symm ▸ hbij
  have hThinD := ThinBallGeometry.annulus_thin d hd
  have hInf := ThinBallGeometry.thin_infinite h00 δ hδ1 d hThinD
  rcases hc with hVF | ⟨a,ha⟩ | ⟨a,α,ha⟩
  · exact OpenBallConstancy.atomic_not_contains_vf B hA (hVF.symm ▸ Set.Subset.rfl)
  · have hFin : (f '' A).Finite := by
      rw [ha]
      exact (Set.finite_singleton a.val).image f
    exact hInf (Eq.mp (congrArg Set.Finite hBijD.image_eq) hFin)
  · let c := ThinBallGeometry.closedComponent a α
    have hBodyC : c.body = A := (ThinBallGeometry.closed_body a α).trans ha.symm
    have hBallA : IsBall A := ha.symm ▸ BallEnlargementGeometry.gammaBall_isBall a α false
    have hOO := AtomicOpenToOpen.open_to_open B h00 δ hδ hδ1 hA hD
      (isBall_subset_vf A hBallA) d.body_subset_vf f hf hBijD
    have hfC : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn c.body f) := hBodyC.symm ▸ hf
    have hbC : Set.BijOn f c.body d.body := hBodyC.symm ▸ hBijD
    have hoC : MaximalOpenClasses.OpenToOpen c.body f := hBodyC.symm ▸ hOO
    have hCounts := ThinBallHoleConservation.holes_eq B δ hδ1 c d
      (ThinBallGeometry.closed_thin a α) hThinD f hfC hbC hoC
    have hZero : c.holes.card = 0 := rfl
    obtain ⟨u,v,β,_,hHoles⟩ := hd
    have hOne : d.holes.card = 1 := by rw [hHoles,Finset.card_singleton]
    exact (zero_ne_one : (0 : ℕ) ≠ 1) (hZero.symm.trans (hCounts.trans hOne))

theorem proposition_3_23 (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : AdjoinBall.AtomicOver B A) (hC : AdjoinBall.AtomicOver B C)
    (k l : PaperBalls.PrimitiveKind) (hk : HasShape k A) (hl : HasShape l C) (hne : k ≠ l)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) : False := by
  let g := RVInverse.inverse A f
  have hImage : f '' A = C := hbij.image_eq
  have hgGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn C g) := by
    have hg := RVInverse.inverse_graph_definable B hbij.2.1 hf
    rwa [hImage] at hg
  have hgBij : Set.BijOn g C A := inverse_bijOn f hbij
  cases k <;> cases l
  · exact hne rfl
  · exact no_open_target B h00 δ hδ hδ1 hA hC hk (Or.inl hl) f hf hbij
  · exact no_open_target B h00 δ hδ hδ1 hA hC hk (Or.inr hl) f hf hbij
  · exact no_open_target B h00 δ hδ hδ1 hC hA hl (Or.inl hk) g hgGraph hgBij
  · exact hne rfl
  · exact no_closed_thin B h00 δ hδ hδ1 hA hC hk hl f hf hbij
  · exact no_open_target B h00 δ hδ hδ1 hC hA hl (Or.inr hk) g hgGraph hgBij
  · exact no_closed_thin B h00 δ hδ hδ1 hC hA hl hk g hgGraph hgBij
  · exact hne rfl

end IntegrationInACVF.Section3ACVF.AtomicPrimitiveDistinction
