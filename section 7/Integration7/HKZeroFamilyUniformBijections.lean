module

public import Integration7.HKZeroFamilyRowIsomorphisms
public import Integration7.HKMixedFibreConstraintRealization
public import Integration7.GammaMixedIsomorphismMaps
public import Integration7.VFVolumeBijections
public import Integration7.VFVolumeClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact weighted row equality glues to an actual original-base volume
bijection, with the RV density retained by the compactness constraint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaIso gammaLogicInput pointSpace PresentedSet setDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

theorem zero_volume_family_uniform_bijection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (h : ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    Nonempty (VFVolumeBijection F.fullVFObject G.fullVFObject) := by
  let B : Base (M := M) := ⟨(C.base : Set M),∅⟩
  have hg : Cardinal.mk B.gamma < C.κ := by
    simpa [B] using (Cardinal.aleph0_pos.trans C.uncountable)
  have hA := (gammaLogicInput B).real_set _
    (setDefinable (PresentedSet.univ (pointSpace (M := M) (n+1) 0) (C.base : Set M)))
  have hF := (gammaLogicInput B).real_set _ (setDefinable (nativeMixedVolumeDomain hc F.domain))
  have hG := (gammaLogicInput B).real_set _ (setDefinable (nativeMixedVolumeDomain hc G.domain))
  obtain ⟨e,he,heR⟩ := gamma_mixed_fibre_constrained_restricted
    C.uncountable.le C.saturated C.small hg Set.univ hA F.domain.carrier G.domain.carrier hF hG
    (densityEqualRelation F.form G.form) (density_equal_gamma_graph hc F.form G.form) (by
      intro x
      exact zero_volume_family_row_gamma_iso hc F G x.val.1 (h x.val.1))
  have hU : {q | (q.1,Fin.elim0) ∈ (Set.univ : Set (Point (M := M) (n+1) 0)) ∧ q ∈ F.domain.carrier} =
      F.domain.carrier := Set.ext (fun _ => ⟨And.right,fun h => ⟨Set.mem_univ _,h⟩⟩)
  have hV : {q | (q.1,Fin.elim0) ∈ (Set.univ : Set (Point (M := M) (n+1) 0)) ∧ q ∈ G.domain.carrier} =
      G.domain.carrier := Set.ext (fun _ => ⟨And.right,fun h => ⟨Set.mem_univ _,h⟩⟩)
  let g := e.congr hU hV
  have hgVF := vfParametersPreserved_congr (p := n+1) (n := 0) (m := 0) e he hU hV
  have hgR : ∀ u, densityEqualRelation F.form G.form u.val (g.equiv u).val := by
    intro u
    rw [gammaIsoCongr_value]
    exact heR ((Equiv.subtypeEquivRight (fun q => Iff.of_eq
      (congrArg (fun S => q ∈ S) hU))).symm u)
  have hNames : commonRealNames B ⊆ (C.base : Set M) := by
    simp [B,commonRealNames]
  let f := gammaMixedIsoMap hc g hNames
  refine ⟨VFVolumeBijection.of_preserving_vf_and_density hc C f
    (gammaMixedIsoMap_bijective hc g hNames) ?_ ?_⟩
  · intro q
    funext j
    exact hgVF q j
  · intro q
    obtain ⟨r,s,hr,hs,hρ⟩ := hgR q
    have hr' : r = q := Subtype.ext hr
    have hs' : s = f q := Subtype.ext hs
    exact (congrArg F.form.value hr'.symm).trans (hρ.trans (congrArg G.form.value hs'))

theorem zero_volume_full_class_eq_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (h : ∀ x, rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x)) :
    positiveVFVolumeIsoClass hc C F.fullVFObject = positiveVFVolumeIsoClass hc C G.fullVFObject := by
  obtain ⟨e⟩ := zero_volume_family_uniform_bijection hc F G h
  exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨VFVolumeIso.of_bijection e⟩

end IntegrationInACVF.Section7.HK
