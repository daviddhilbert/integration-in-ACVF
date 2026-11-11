import IntegrationSection3ACVF.AnnulusValueIntervals
import IntegrationSection3ACVF.ClosedSelfCentredBallProfiles
import IntegrationSection3ACVF.SelfCentredBallProfiles

/-! Exact value images for actual single-hole punctured balls after
translating a point of the hole to zero. The parent centre need not equal
the hole centre. VF is retained as a possible open target parent. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PuncturedBallValueIntervals

open GammaRadiusAtomicity PuncturedGeometry AnnulusValueIntervals

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem body_single_hole (d : PuncturedBall M) (H : Set M) (hH : d.holes = {H}) :
    d.body = d.parent \ H := by
  ext z
  change (z ∈ d.parent ∧ ¬ ∃ h ∈ d.holes, z ∈ h) ↔ _
  rw [hH]
  simp only [Finset.mem_singleton,exists_eq_left,Set.mem_diff]

theorem closed_parent (d : PuncturedBall M) (a c : VFType (M := M))
    (ρ τ : Values.Gamma (M := M)) (hParent : d.parent = gammaBall a ρ false)
    (hHoles : d.holes = {gammaBall c τ true}) :
    valueImage c d.body = Set.Icc ρ.val τ.val := by
  have hMem : gammaBall c τ true ∈ d.holes := hHoles.symm ▸ Finset.mem_singleton_self _
  have hc : c.val ∈ gammaBall a ρ false := hParent ▸ (d.holes_proper _ hMem).1
    (BallEnlargementGeometry.gammaBall_centre_mem c τ true)
  rw [body_single_hole d _ hHoles,hParent,← ClosedSelfCentredBallProfiles.centre_change a c ρ hc]
  exact closed_image c ρ τ

theorem open_parent (d : PuncturedBall M) (a c : VFType (M := M))
    (ρ τ : Values.Gamma (M := M)) (hParent : d.parent = gammaBall a ρ true)
    (hHoles : d.holes = {gammaBall c τ true}) :
    valueImage c d.body = Set.Ioc ρ.val τ.val := by
  have hMem : gammaBall c τ true ∈ d.holes := hHoles.symm ▸ Finset.mem_singleton_self _
  have hc : c.val ∈ gammaBall a ρ true := hParent ▸ (d.holes_proper _ hMem).1
    (BallEnlargementGeometry.gammaBall_centre_mem c τ true)
  rw [body_single_hole d _ hHoles,hParent,← SelfCentredBallProfiles.centre_change a c ρ hc]
  exact open_image c ρ τ

theorem whole_field_parent (d : PuncturedBall M) (c : VFType (M := M))
    (τ : Values.Gamma (M := M)) (hParent : d.parent = {x | iVF x})
    (hHoles : d.holes = {gammaBall c τ true}) :
    valueImage c d.body = Set.Iic τ.val := by
  rw [body_single_hole d _ hHoles,hParent]
  exact whole_field_image c τ

end IntegrationInACVF.Section3ACVF.PuncturedBallValueIntervals
