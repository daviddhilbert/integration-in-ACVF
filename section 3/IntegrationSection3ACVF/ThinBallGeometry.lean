import IntegrationSection3ACVF.ThinBallHoleConservation
import IntegrationSection3ACVF.SeparationFunctions

/-! Actual closed components, thin annuli and infinitude of thin bodies. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.ThinBallGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def closedComponent (a : VFType (M := M)) (α : Values.Gamma (M := M)) : PuncturedBall M where
  parent := gammaBall a α false
  parent_ball := BallEnlargementGeometry.gammaBall_isBall a α false
  holes := ∅
  holes_ball := by simp
  holes_proper := by simp
  holes_disjoint := by simp

theorem closed_body (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    (closedComponent a α).body = gammaBall a α false := by
  ext x
  simp only [closedComponent,PuncturedBall.body,Finset.notMem_empty,false_and,exists_false,
    Set.ofPred_false,Set.sdiff_empty]

theorem closed_thin (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    IsThin (closedComponent a α) := by
  refine ⟨a,α,rfl,?_⟩
  intro h hh
  exact (Finset.notMem_empty h hh).elim

theorem annulus_thin (d : PuncturedBall M) (hd : PaperBalls.IsThinAnnulus d) : IsThin d := by
  obtain ⟨a,b,α,hp,hh⟩ := hd
  refine ⟨a,α,hp,?_⟩
  intro h hh'
  rw [hh] at hh'
  exact ⟨b,Finset.mem_singleton.mp hh'⟩

theorem thin_infinite (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (hd : IsThin d) : d.body.Infinite := by
  obtain ⟨a,α,hp,hh⟩ := hd
  obtain ⟨x,hx⟩ := SeparationFunctions.punctured_nonempty δ hδ d
  obtain ⟨j,hj,_⟩ := MaximalSubballGeometry.covers_body d α a hp hh x hx
  obtain ⟨b,hb⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ hj.1.1 α hj.1.2
  have ho : PaperBalls.IsOpenBall (BallImaginaries.underlying j) := Or.inr ⟨b,α,hb⟩
  exact (SeparationFunctions.open_infinite h00 δ hδ ho).mono hj.2

end IntegrationInACVF.Section3ACVF.ThinBallGeometry
