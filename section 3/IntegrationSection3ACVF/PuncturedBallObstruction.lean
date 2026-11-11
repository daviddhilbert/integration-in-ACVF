import IntegrationSection3ACVF.AnnulusGammaReduction
import IntegrationSection3ACVF.GammaIntervalObstruction
import IntegrationSection3ACVF.PuncturedSingleHole

/-! Proposition3.24 with the author-approved ordinary closed-parent
correction. The open target retains VF. Every actual quotient graph,
Gamma matching and finite interval count is supplied by checked proofs. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PuncturedBallObstruction

open PuncturedGeometry GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ordinary_presentations {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (d e : PuncturedBall M) (a c k : VFType (M := M)) (ρ τ ν : Values.Gamma (M := M))
    (hParent : d.parent = gammaBall a ρ false) (hHoles : d.holes = {gammaBall c τ true})
    (hOpen : PaperBalls.IsOpenBall e.parent) (hEHoles : e.holes = {gammaBall k ν true})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hBij : Set.BijOn f d.body e.body) : ¬ MaximalOpenClasses.OpenToOpen d.body f := by
  intro hoo
  have hρτ := PuncturedSingleHole.closed_radius_le d a c ρ τ hParent hHoles
  obtain ⟨J,hJ,q,hBijQ,hGraphQ⟩ := AnnulusGammaReduction.closed_to_open hκ hs h00 B hsmall
    d e a c k ρ τ ν hParent hHoles hOpen hEHoles f hf hBij hoo
  exact GammaIntervalObstruction.no_subtype_bijection hκ hs h00
    (RealParameterTuples.extend B ![c.val,k.val]) (RealParameterTuples.small hκ B hsmall ![c.val,k.val])
    ρ τ ν hρτ J hJ q hBijQ hGraphQ

theorem proposition_3_24 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (d e : PuncturedBall M)
    (hClosed : ∃ a : VFType (M := M), ∃ ρ : Values.Gamma (M := M), d.parent = gammaBall a ρ false)
    (hOpen : PaperBalls.IsOpenBall e.parent)
    (hDCard : d.holes.card = 1) (hDOpen : ∀ H ∈ d.holes, PaperBalls.IsOpenBall H)
    (hECard : e.holes.card = 1) (hEOpen : ∀ H ∈ e.holes, PaperBalls.IsOpenBall H)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hBij : Set.BijOn f d.body e.body) : ¬ MaximalOpenClasses.OpenToOpen d.body f := by
  obtain ⟨a,ρ,hParent⟩ := hClosed
  obtain ⟨c,τ,hHoles⟩ := PuncturedSingleHole.ordinary_hole d hDCard hDOpen
  obtain ⟨k,ν,hEHoles⟩ := PuncturedSingleHole.ordinary_hole e hECard hEOpen
  exact ordinary_presentations hκ hs h00 B hsmall d e a c k ρ τ ν hParent hHoles hOpen hEHoles f hf hBij

end IntegrationInACVF.Section3ACVF.PuncturedBallObstruction
