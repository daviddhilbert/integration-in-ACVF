import IntegrationSection3ACVF.RadialAnnulusDomains

/-! Every single proper paper-open hole is ordinary, and its removal
leaves a nonempty actual body. Ordinary closed sources have ordered
Gamma endpoints, including the equal-radius thin-annulus case. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.PuncturedSingleHole

open PuncturedGeometry GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ordinary_hole (d : PuncturedBall M) (hCard : d.holes.card = 1)
    (hOpen : ∀ H ∈ d.holes, PaperBalls.IsOpenBall H) :
    ∃ c : VFType (M := M), ∃ τ : Values.Gamma (M := M), d.holes = {gammaBall c τ true} := by
  obtain ⟨H,hH⟩ := Finset.card_eq_one.mp hCard
  have hMem : H ∈ d.holes := hH.symm ▸ Finset.mem_singleton_self H
  rcases hOpen H hMem with hVF | ⟨c,τ,hBall⟩
  · have hProper := d.holes_proper H hMem
    have hSub : d.parent ⊆ H := by
      rw [hVF]
      exact isBall_subset_vf d.parent d.parent_ball
    exact (hProper.2 hSub).elim
  · exact ⟨c,τ,hBall ▸ hH⟩

theorem body_nonempty (d : PuncturedBall M) (H : Set M) (hH : d.holes = {H}) : d.body.Nonempty := by
  have hMem : H ∈ d.holes := hH.symm ▸ Finset.mem_singleton_self H
  obtain ⟨x,hxParent,hxHole⟩ := Set.exists_of_ssubset (d.holes_proper H hMem)
  refine ⟨x,hxParent,?_⟩
  rintro ⟨K,hK,hxK⟩
  have hEq : K = H := Finset.mem_singleton.mp (hH ▸ hK)
  exact hxHole (hEq ▸ hxK)

theorem closed_radius_le (d : PuncturedBall M) (a c : VFType (M := M))
    (ρ τ : Values.Gamma (M := M)) (hParent : d.parent = gammaBall a ρ false)
    (hHoles : d.holes = {gammaBall c τ true}) : ρ ≤ τ := by
  obtain ⟨z,hz⟩ := body_nonempty d _ hHoles
  rw [RadialAnnulusDomains.punctured_closed d a c ρ τ hParent hHoles] at hz
  obtain ⟨_,hBounds⟩ := hz
  exact hBounds.1.trans hBounds.2

end IntegrationInACVF.Section3ACVF.PuncturedSingleHole
