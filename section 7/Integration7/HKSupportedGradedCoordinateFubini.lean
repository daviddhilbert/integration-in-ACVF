module

public import Integration7.HKGradedVolumeCoordinateFubini
public import Integration7.HKVolumeComponentSupports

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Coordinate integration restricts to the actual supported graded
functions and lands on the literal projected support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def gradedVolumeSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    AddSubmonoid (GradedAEVolumeFunction hc C n) where
  carrier := Set.range (supportedGradedVolumeForgetAddHom hc C X)
  zero_mem' := ⟨0,map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨f+g,map_add _ f g⟩

theorem graded_volume_generator_has_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) (hf : HasVolumeComponentSupport hc C X j f) :
    DirectSum.of _ j f ∈ gradedVolumeSupport hc C X := by
  obtain ⟨g,rfl⟩ := hf
  exact ⟨DirectSum.of _ j g,supported_graded_volume_forget_of hc C X j g⟩

theorem graded_volume_base_preserves_support {a b : ℕ} (h : a=b)
    (X : DefSet (rawVFSpace (M := M) (b+1)) (C.base : Set M))
    (f : GradedAEVolumeFunction hc C b) (hf : f ∈ gradedVolumeSupport hc C X) :
    gradedAEVolumeBaseEquiv hc C h f ∈
      gradedVolumeSupport hc C (pureVFCoordinateImage X (finCongr (congrArg Nat.succ h))) := by
  cases h
  change f ∈ gradedVolumeSupport hc C (pureVFCoordinateImage X id)
  rw [pure_vf_coordinate_image_id]
  exact hf

theorem graded_volume_coordinate_permutation_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1)))
    (f : GradedAEVolumeFunction hc C n) (hf : f ∈ gradedVolumeSupport hc C X) :
    gradedAEVolumeCoordinatePermutationAddHom hc C σ f ∈
      gradedVolumeSupport hc C (pureVFCoordinateImage X σ) := by
  obtain ⟨g,rfl⟩ := hf
  induction g using DirectSum.induction_on with
  | zero => simpa only [map_zero] using (gradedVolumeSupport hc C _).zero_mem
  | add f g hf hg =>
    simp only [map_add]
    exact (gradedVolumeSupport hc C _).add_mem hf hg
  | of j f =>
    change gradedAEVolumeJacobianAddHom hc C _ _
      (supportedGradedVolumeForgetAddHom hc C X (DirectSum.of _ j f)) ∈ _
    rw [supported_graded_volume_forget_of,graded_ae_volume_jacobian_of]
    exact graded_volume_generator_has_support hc C _ j _
      (volume_component_coordinate_jacobian_preserves_support hc C X σ j _ ⟨f,rfl⟩)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem graded_volume_head_preserves_support
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M))
    (f : GradedAEVolumeFunction hc C (n+1)) (hf : f ∈ gradedVolumeSupport hc C X) :
    gradedAEVolumeHeadIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f ∈
      gradedVolumeSupport hc C (pureVFCoordinateImage X Fin.succ) := by
  obtain ⟨g,rfl⟩ := hf
  induction g using DirectSum.induction_on with
  | zero => simpa only [map_zero] using (gradedVolumeSupport hc C _).zero_mem
  | add f g hf hg =>
    simp only [map_add]
    exact (gradedVolumeSupport hc C _).add_mem hf hg
  | of j f =>
    rw [supported_graded_volume_forget_of,graded_ae_volume_head_integral_of]
    exact graded_volume_generator_has_support hc C _ (j+1) _
      (volume_component_head_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X j _ ⟨f,rfl⟩)

theorem graded_volume_prefix_preserves_support : ∀ (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M))
    (f : GradedAEVolumeFunction hc C (n+r)), f ∈ gradedVolumeSupport hc C X →
    gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f ∈
      gradedVolumeSupport hc C (pureVFPrefixImage r n X) := by
  intro r
  induction r with
  | zero => intro n X f hf; exact hf
  | succ r ih =>
    intro n X f hf
    exact ih n (pureVFCoordinateImage X Fin.succ) _
      (graded_volume_head_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f hf)

theorem graded_volume_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : GradedAEVolumeFunction hc C n) (hf : f ∈ gradedVolumeSupport hc C X) :
    gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f ∈
      gradedVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex) := by
  have hCast := graded_volume_base_preserves_support hc C (volume_projection_index_eq E) X f hf
  have hPerm := graded_volume_coordinate_permutation_preserves_support hc C _ (volumeProjectionFibreOrder E) _ hCast
  have hPrefix := graded_volume_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    E.discarded p _ _ hPerm
  rw [volume_projection_iterated_image] at hPrefix
  exact hPrefix

def supportedGradedCoordinateIntegralAddHom
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) :
    gradedVolumeSupport hc C X →+ gradedVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex) where
  toFun f := ⟨gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f.val,
    graded_volume_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f.val f.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' f g := Subtype.ext (map_add _ f.val g.val)

theorem supported_graded_coordinate_total_fubini
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : gradedVolumeSupport hc C X) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (supportedGradedCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f).val =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f.val :=
  graded_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f.val

end IntegrationInACVF.Section7.HK
