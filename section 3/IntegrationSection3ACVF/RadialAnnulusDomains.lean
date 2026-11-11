import IntegrationSection3ACVF.RadialRVImages
import IntegrationSection3ACVF.PuncturedBallValueIntervals

/-! Actual single-hole annuli are exactly radial value domains. This
pointwise identification complements the already checked exact value images
and permits the full definable RV/Gamma quotient theorems to be applied. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialAnnulusDomains

open GammaRadiusAtomicity PuncturedGeometry AnnulusValueIntervals

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem closed_domain (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    gammaBall a ρ false \ gammaBall a τ true = RadialOpenClasses.domain a (Set.Icc ρ.val τ.val) := by
  ext z
  constructor
  · rintro ⟨hParent,hHole⟩
    let x : VFType (M := M) := ⟨z,hParent.choose⟩
    refine (RadialOpenClasses.mem_domain a x _).mpr ⟨(mem_closed a x ρ).mp hParent,?_⟩
    exact le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))
  · rintro ⟨hz,hBounds⟩
    let x : VFType (M := M) := ⟨z,hz⟩
    refine ⟨(mem_closed a x ρ).mpr hBounds.1,?_⟩
    intro hHole
    exact (not_lt_of_ge hBounds.2) ((mem_open a x τ).mp hHole)

theorem open_domain (a : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) :
    gammaBall a ρ true \ gammaBall a τ true = RadialOpenClasses.domain a (Set.Ioc ρ.val τ.val) := by
  ext z
  constructor
  · rintro ⟨hParent,hHole⟩
    let x : VFType (M := M) := ⟨z,hParent.choose⟩
    refine (RadialOpenClasses.mem_domain a x _).mpr ⟨(mem_open a x ρ).mp hParent,?_⟩
    exact le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))
  · rintro ⟨hz,hBounds⟩
    let x : VFType (M := M) := ⟨z,hz⟩
    refine ⟨(mem_open a x ρ).mpr hBounds.1,?_⟩
    intro hHole
    exact (not_lt_of_ge hBounds.2) ((mem_open a x τ).mp hHole)

theorem whole_field_domain (a : VFType (M := M)) (τ : Values.Gamma (M := M)) :
    {x | iVF x} \ gammaBall a τ true = RadialOpenClasses.domain a (Set.Iic τ.val) := by
  ext z
  constructor
  · rintro ⟨hz,hHole⟩
    let x : VFType (M := M) := ⟨z,hz⟩
    refine (RadialOpenClasses.mem_domain a x _).mpr ?_
    exact le_of_not_gt (fun h => hHole ((mem_open a x τ).mpr h))
  · rintro ⟨hz,hBound⟩
    let x : VFType (M := M) := ⟨z,hz⟩
    refine ⟨hz,?_⟩
    intro hHole
    exact (not_lt_of_ge hBound) ((mem_open a x τ).mp hHole)

theorem punctured_closed (d : PuncturedBall M) (a c : VFType (M := M))
    (ρ τ : Values.Gamma (M := M)) (hParent : d.parent = gammaBall a ρ false)
    (hHoles : d.holes = {gammaBall c τ true}) : d.body = RadialOpenClasses.domain c (Set.Icc ρ.val τ.val) := by
  have hMem : gammaBall c τ true ∈ d.holes := hHoles.symm ▸ Finset.mem_singleton_self _
  have hc : c.val ∈ gammaBall a ρ false := hParent ▸ (d.holes_proper _ hMem).1
    (BallEnlargementGeometry.gammaBall_centre_mem c τ true)
  rw [PuncturedBallValueIntervals.body_single_hole d _ hHoles,hParent,
    ← ClosedSelfCentredBallProfiles.centre_change a c ρ hc]
  exact closed_domain c ρ τ

theorem punctured_open (d : PuncturedBall M) (a c : VFType (M := M))
    (ρ τ : Values.Gamma (M := M)) (hParent : d.parent = gammaBall a ρ true)
    (hHoles : d.holes = {gammaBall c τ true}) : d.body = RadialOpenClasses.domain c (Set.Ioc ρ.val τ.val) := by
  have hMem : gammaBall c τ true ∈ d.holes := hHoles.symm ▸ Finset.mem_singleton_self _
  have hc : c.val ∈ gammaBall a ρ true := hParent ▸ (d.holes_proper _ hMem).1
    (BallEnlargementGeometry.gammaBall_centre_mem c τ true)
  rw [PuncturedBallValueIntervals.body_single_hole d _ hHoles,hParent,
    ← SelfCentredBallProfiles.centre_change a c ρ hc]
  exact open_domain c ρ τ

theorem punctured_whole_field (d : PuncturedBall M) (c : VFType (M := M))
    (τ : Values.Gamma (M := M)) (hParent : d.parent = {x | iVF x})
    (hHoles : d.holes = {gammaBall c τ true}) : d.body = RadialOpenClasses.domain c (Set.Iic τ.val) := by
  rw [PuncturedBallValueIntervals.body_single_hole d _ hHoles,hParent]
  exact whole_field_domain c τ

end IntegrationInACVF.Section3ACVF.RadialAnnulusDomains
