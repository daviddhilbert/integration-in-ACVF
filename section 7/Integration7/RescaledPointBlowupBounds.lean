import Integration7.OrdinaryHeadFactorBoundary
import Integration7.BlowupGammaUpperBounds
import Integration7.VolumeBlowupClasses

/-! Absolute densities of actual degree-one points remain distinguished
by common blowups. This is a semiring-level boundary, not a claim about
the kernel after groupification or generation of its ideal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
local notation "Abs" => MonoidWithZeroHom.ValueGroup₀
  (MonoidWithZeroHom.ofClass (Values.presentationValuation (M := M)))

private def rescaledPointEssentialLabel (c : CanonicalRV.RVSort M) (hS : c.val ∈ S) (h0 : c ≠ 0) :
    ((degreeOnePointVolumeObject S).rescale c hS h0).essential.obj.domain := by
  let U := (degreeOnePointVolumeObject S).rescale c hS h0
  let u0 : U.underlying.obj.domain := ⟨Fin.elim0,Set.mem_univ _⟩
  refine ⟨u0.val,(mem_rvEssentialLabels U.underlying.obj u0).mpr ?_⟩
  intro i
  exact (rv_nonzero_iff_raw _).mp one_ne_zero

theorem rescaled_point_essential_weight (c : CanonicalRV.RVSort M) (hS : c.val ∈ S) (h0 : c ≠ 0)
    (u : ((degreeOnePointVolumeObject S).rescale c hS h0).essential.obj.domain) :
    essentialGammaWeight ((degreeOnePointVolumeObject S).rescale c hS h0) u = RVOperations.absoluteHom c := by
  change RVOperations.absoluteHom (c * 1) *
    (∏ _ : Fin 1, RVOperations.absoluteHom (1 : CanonicalRV.RVSort M)) = RVOperations.absoluteHom c
  simp only [mul_one,Fin.prod_univ_one,map_one]

theorem rescaled_point_upper_bound_iff (c : CanonicalRV.RVSort M) (hS : c.val ∈ S) (h0 : c ≠ 0) (a : Abs) :
    essentialGammaUpperBound ((degreeOnePointVolumeObject S).rescale c hS h0) a ↔ RVOperations.absoluteHom c ≤ a := by
  constructor
  · intro h
    simpa only [rescaled_point_essential_weight] using h (rescaledPointEssentialLabel c hS h0)
  · intro h u
    rw [rescaled_point_essential_weight]
    exact h

theorem rescaled_points_blowup_equivalent_absolute_eq (c d : CanonicalRV.RVSort M)
    (hcS : c.val ∈ S) (hc0 : c ≠ 0) (hdS : d.val ∈ S) (hd0 : d ≠ 0)
    (h : VolumeBlowupEquivalent ((degreeOnePointVolumeObject S).rescale c hcS hc0)
      ((degreeOnePointVolumeObject S).rescale d hdS hd0)) :
    RVOperations.absoluteHom c = RVOperations.absoluteHom d := by
  have hcA : RVOperations.absoluteHom c ≠ 0 := (RVOperations.absolute_eq_zero _).not.mpr hc0
  have hdA : RVOperations.absoluteHom d ≠ 0 := (RVOperations.absolute_eq_zero _).not.mpr hd0
  have hC := (rescaled_point_upper_bound_iff c hcS hc0 _).mpr (le_refl _)
  have hD := (rescaled_point_upper_bound_iff d hdS hd0 _).mpr (le_refl _)
  exact le_antisymm
    ((rescaled_point_upper_bound_iff c hcS hc0 _).mp
      ((h.essentialGammaUpperBound _ hdA).mpr hD))
    ((rescaled_point_upper_bound_iff d hdS hd0 _).mp
      ((h.essentialGammaUpperBound _ hcA).mp hC))

theorem rescaled_point_classes_unequal (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (c d : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)
    (hdS : d.val ∈ C.base) (hd0 : d ≠ 0) (hAbs : RVOperations.absoluteHom c ≠ RVOperations.absoluteHom d) :
    positiveVolumeBlowupClass hc C ((degreeOnePointVolumeObject (C.base : Set M)).rescale c hcS hc0) ≠
      positiveVolumeBlowupClass hc C ((degreeOnePointVolumeObject (C.base : Set M)).rescale d hdS hd0) := by
  intro h
  exact hAbs (rescaled_points_blowup_equivalent_absolute_eq c d hcS hc0 hdS hd0
    ((positiveVolumeBlowupClass_eq_iff hc C).mp h))
end IntegrationInACVF.Section7
