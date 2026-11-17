module

public import Integration7.OrdinaryVolumeFamilyUniformBijections
public import Integration7.DensityGraphRelativeBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The ordinary finite-fibre uniformity comparison retains its stronger
coordinate conclusion: every VF coordinate is fixed by the actual map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaIso gammaLogicInput pointSpace PresentedSet setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

theorem ordinary_volume_family_bijection_fixing_vf
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : OrdinaryVFVolumeFamily C (n+1) a) (G : OrdinaryVFVolumeFamily C (n+1) b)
    (h : ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    ∃ e : VFVolumeBijection F.fullVFObject G.fullVFObject,
      ∀ q j, (e.map q).val.1 j = q.val.1 j := by
  let B : Base (M := M) := ⟨(C.base : Set M),∅⟩
  have hg : Cardinal.mk B.gamma < C.κ := by
    simpa [B] using (Cardinal.aleph0_pos.trans C.uncountable)
  have hA := (gammaLogicInput B).real_set _
    (setDefinable (PresentedSet.univ (pointSpace (M := M) (n+1) 0) (C.base : Set M)))
  have hF := (gammaLogicInput B).real_set _ (setDefinable (nativeMixedVolumeDomain hc F.domain))
  have hG := (gammaLogicInput B).real_set _ (setDefinable (nativeMixedVolumeDomain hc G.domain))
  obtain ⟨e,he⟩ := gamma_mixed_fibre_uniformity (p := n+1) (n := 0) (m := 0)
    C.uncountable.le C.saturated C.small hg Set.univ hA F.domain.carrier G.domain.carrier hF hG
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) (by
      intro x
      exact ordinary_volume_family_row_gamma_iso hc F G x.val.1 (h x.val.1))
  have hNames : commonRealNames B ⊆ (C.base : Set M) := by
    simp [B,commonRealNames]
  let f := gammaMixedIsoMap hc e hNames
  let E : VFVolumeBijection F.fullVFObject G.fullVFObject :=
    VFVolumeBijection.of_preserving_vf_and_density hc C f
      (gammaMixedIsoMap_bijective hc e hNames) (fun q => funext (he q)) (fun _ => rfl)
  exact ⟨E,he⟩

end IntegrationInACVF.Section7
