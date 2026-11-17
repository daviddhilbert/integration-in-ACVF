module

public import Integration7.RawSupportedGradedCoordinateIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Supported raw Fubini for every nonempty coordinate subset. The full
set retains its original order, so the identity case introduces neither
a degree-zero density nor an arbitrary permutation of ordinary values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem raw_supported_volume_base_preserves_support {a b : ℕ} (h : a=b)
    (X : DefSet (rawVFSpace (M := M) (b+1)) (C.base : Set M))
    (f : GradedAEVolumeFunction hc C b) (hf : f ∈ rawSupportedVolumeSubmodule hc C X) :
    gradedAEVolumeBaseEquiv hc C h f ∈
      rawSupportedVolumeSubmodule hc C (pureVFCoordinateImage X (finCongr (congrArg Nat.succ h))) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j,f,hf,rfl⟩ := hg
    rw [graded_ae_volume_base_equiv_of]
    exact raw_supported_volume_generator_mem hc C _ j _ (raw_volume_component_base_preserves_support hc C h X j f hf)
  | zero => simpa only [map_zero] using (rawSupportedVolumeSubmodule hc C _).zero_mem
  | add f g hf hg ihf ihg =>
    rw [map_add]
    exact (rawSupportedVolumeSubmodule hc C _).add_mem ihf ihg
  | smul r f hf ih =>
    rw [map_smul]
    exact (rawSupportedVolumeSubmodule hc C _).smul_mem r ih

omit hc C in
def rawNonemptyVolumeRetainedIndex (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    Fin (rawNonemptyVolumeCoordinateDimension E+1) → Fin (n+1) := by
  by_cases h : E=Set.univ
  · exact fun j => finCongr (congrArg Nat.succ (show rawNonemptyVolumeCoordinateDimension E=n by
      simp [rawNonemptyVolumeCoordinateDimension,h])) j
  · exact (nonemptyVolumeCoordinateProjection E hE).retainedIndex ∘
      finCongr (congrArg Nat.succ (show rawNonemptyVolumeCoordinateDimension E=(Fintype.card E).pred by
        simp [rawNonemptyVolumeCoordinateDimension,h]))

omit hc C in
theorem raw_nonempty_volume_retained_range (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    Set.range (rawNonemptyVolumeRetainedIndex E hE)=E := by
  by_cases h : E=Set.univ
  · simp only [rawNonemptyVolumeRetainedIndex,dif_pos h]
    exact (Equiv.range_eq_univ _).trans h.symm
  · simp only [rawNonemptyVolumeRetainedIndex,dif_neg h]
    rw [Set.range_comp,Equiv.range_eq_univ,Set.image_univ]
    exact nonempty_volume_coordinate_projection_range E hE

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_nonempty_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty)
    (f : GradedAEVolumeFunction hc C n) (hf : f ∈ rawSupportedVolumeSubmodule hc C X) :
    rawNonemptyVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f ∈
      rawSupportedVolumeSubmodule hc C (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE)) := by
  by_cases h : E=Set.univ
  · simpa only [rawNonemptyVolumeCoordinatePushforward,rawNonemptyVolumeRetainedIndex,dif_pos h,LinearEquiv.coe_toLinearMap] using
      raw_supported_volume_base_preserves_support hc C
        (show rawNonemptyVolumeCoordinateDimension E=n by simp [rawNonemptyVolumeCoordinateDimension,h]) X f hf
  · have hP := raw_strict_volume_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X
      (nonemptyVolumeCoordinateProjection E hE) (proper_nonempty_volume_projection_discards E hE h) f hf
    have hB := raw_supported_volume_base_preserves_support hc C
      (show rawNonemptyVolumeCoordinateDimension E=(Fintype.card E).pred by simp [rawNonemptyVolumeCoordinateDimension,h])
      _ _ hP
    rw [pure_vf_coordinate_image_comp] at hB
    simpa only [rawNonemptyVolumeCoordinatePushforward,rawNonemptyVolumeRetainedIndex,dif_neg h,
      LinearMap.comp_apply,rawStrictVolumeCoordinateIntegral,LinearEquiv.coe_toLinearMap] using hB

def rawSupportedNonemptyCoordinateIntegral
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    rawSupportedVolumeSubmodule hc C X →ₗ[RVVolumeBlowupSemiring hc C]
      rawSupportedVolumeSubmodule hc C (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE)) :=
  LinearMap.codRestrict _
    ((rawNonemptyVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE).comp
      (rawSupportedVolumeSubmodule hc C X).subtype)
    (fun f => raw_nonempty_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE f.val f.property)

theorem raw_supported_nonempty_coordinate_total_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    (rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (pureVFCoordinateImage X (rawNonemptyVolumeRetainedIndex E hE))).comp
      (rawSupportedNonemptyCoordinateIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E hE) =
      rawSupportedGradedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  exact raw_nonempty_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f.val
end IntegrationInACVF.Section7
