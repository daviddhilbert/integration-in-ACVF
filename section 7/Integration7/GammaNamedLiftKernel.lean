import Integration7.GammaNamedDensityLifts
import Integration7.CommonContextVolumeDescent

/-! The Gamma-named lift kernel (forward direction of Proposition 7.8).

For Gamma RV volume objects `U V` over an arbitrary Gamma base `G`, coded in
a context `C` containing the real part and the common names of `G`, a
Gamma almost-everywhere VF volume isomorphism of their lifts yields a Gamma
common volume blowup equivalence over `C.base`. The densities are arbitrary.
Gamma intermediate densities come from `gamma_volume_transport_input`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem rv_volume_lift_common_context_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : GammaVolumeObjects G (C.base : Set M) k)
    (f : VFVolumeIso (rvVolumeLift U.val) (rvVolumeLift V.val)) (hf : f.GammaDefinable G) :
    CommonContextVolumeEquivalent G C U V := by
  let gU := VFVolumeIso.of_bijection (densityGraphLiftBijection hc C U.val)
  let gV := VFVolumeIso.of_bijection (densityGraphLiftBijection hc C V.val)
  have hgU := density_graph_lift_gamma hc C hGC U.property
  have hgV := density_graph_lift_gamma hc C hGC V.property
  let g := (gU.symm hc C).trans hc C (f.trans hc C gV)
  have hg : g.GammaDefinable G := (hgU.symm hc C).trans hc C (hf.trans hc C hgV)
  have hMiddle := rv_volume_lift_coordinate_kernel hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 U.val.densityGraph V.val.densityGraph (U.property.densityGraph hc) (V.property.densityGraph hc)
    (Fin.last U.val.underlying.obj.arity) (Fin.last V.val.underlying.obj.arity)
    U.val.densityGraph_density_last V.val.densityGraph_density_last g hg
  have hLeft : CommonContextVolumeEquivalent G C U ⟨U.val.densityGraph,U.property.densityGraph hc⟩ :=
    .of_iso (rvVolumeDensityGraphIso hc C U.val) (rv_volume_density_graph_iso_gamma hc C U.property)
  have hRight : CommonContextVolumeEquivalent G C V ⟨V.val.densityGraph,V.property.densityGraph hc⟩ :=
    .of_iso (rvVolumeDensityGraphIso hc C V.val) (rv_volume_density_graph_iso_gamma hc C V.property)
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

/-- Gamma-named Proposition 7.8, forward direction, as a Gamma blowup equivalence
over the code set. -/
theorem gamma_volume_blowup_of_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase G) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (U V : GammaVolumeObjects G (C.base : Set M) k)
    (f : VFVolumeIso (rvVolumeLift U.val) (rvVolumeLift V.val)) (hf : f.GammaDefinable G) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) k U V :=
  (rv_volume_lift_common_context_kernel hc C G hGC hΞ hGenerated hNames hGeneric
    γ hγ hγ1 U V f hf).descend hc C hNames

end IntegrationInACVF.Section7.GammaNamed
