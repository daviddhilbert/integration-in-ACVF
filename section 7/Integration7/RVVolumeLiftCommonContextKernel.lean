import Integration7.CoordinateRVVolumeLiftKernel
import Integration7.RVVolumeDensityGraphs
import Integration7.EssentialVolumeLiftIsomorphisms

/-! The actual lift kernel with arbitrary original RV densities.
The proof returns common forward blowups with full original-Gamma
geometry in an explicitly quantified containing real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem rv_volume_lift_common_context_kernel
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (f : VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) :
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      ⟨U,volume_object_gamma_over_real_base hc C Ξ U⟩ ⟨V,volume_object_gamma_over_real_base hc C Ξ V⟩ := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let eU := rvVolumeDensityGraphIso hc C U
  let eV := rvVolumeDensityGraphIso hc C V
  obtain ⟨gU⟩ := eU.nonempty_full_lift_iso hc C Ξ hGenerated
  obtain ⟨gV⟩ := eV.nonempty_full_lift_iso hc C Ξ hGenerated
  let g := (gU.symm hc C).trans hc C (f.trans hc C gV)
  have hMiddle := rv_volume_lift_coordinate_kernel hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    U.densityGraph V.densityGraph (Fin.last U.underlying.obj.arity) (Fin.last V.underlying.obj.arity)
    U.densityGraph_density_last V.densityGraph_density_last g
  have hBase : (C.base : Set M) = (Substructure.closure LRV G.real : Set M) := by
    change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
    rw [Substructure.closure_eq]
  have hLeft : CommonContextVolumeEquivalent G C
      ⟨U,volume_object_gamma_over_real_base hc C Ξ U⟩
      ⟨U.densityGraph,volume_object_gamma_over_real_base hc C Ξ U.densityGraph⟩ :=
    .of_iso eU (eU.gamma_of_term_context hc C hBase)
  have hRight : CommonContextVolumeEquivalent G C
      ⟨V,volume_object_gamma_over_real_base hc C Ξ V⟩
      ⟨V.densityGraph,volume_object_gamma_over_real_base hc C Ξ V.densityGraph⟩ :=
    .of_iso eV (eV.gamma_of_term_context hc C hBase)
  exact hLeft.trans hc (hMiddle.trans hc (hRight.symm hc))

end IntegrationInACVF.Section7
