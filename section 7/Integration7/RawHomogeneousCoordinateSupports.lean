import Integration7.RawPositiveCoordinateSupports
import Integration7.StrictGradedVolumeFubini

/-! Ordinary supported representatives acquire their first volume
coordinate through the actual head contraction. Together with positive
supports this proves support preservation in every homogeneous degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev HasRawOrdinaryVolumeSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : AEOrdinaryRVVolumeFunction hc C n) : Prop :=
  ∃ (a : ℕ) (F : OrdinaryVFVolumeFamily C (n+1) a),
    (∀ q : F.domain, q.val.1 ∈ X.carrier) ∧ Quotient.mk _ ⟨a,F⟩=f

def HasRawVolumeComponentSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    (j : ℕ) → AEVolumeFunctionComponent hc C n j → Prop
  | 0,f => HasRawOrdinaryVolumeSupport hc C X f
  | k+1,f => HasRawPositiveVolumeSupport hc C X f

theorem ordinary_head_integral_has_source
    (Ξ : Set (Values.Gamma (M := M))) (F : OrdinaryVFVolumeFamily C (n+1) a)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (q : (F.headIntegral hc Ξ T).domain) :
    ∃ p : F.domain, p.val.1 ∘ Fin.succ=q.val.1 := by
  obtain ⟨r,hr⟩ := T.contractionMap_surjective ⟨q.val,q.property⟩
  let p := densityGraphProjection F.fullVFObject.form ⟨r.val,r.property⟩
  refine ⟨p,?_⟩
  have hp : p.val.1=r.val.1 := congrArg Prod.fst
    (densityGraphProjection_value F.fullVFObject.form ⟨r.val,r.property⟩)
  funext i
  have hq := congrArg (fun z : T.contractedSet => z.val.1 i) hr
  change (T.map r).val.1 i.succ=q.val.1 i at hq
  rw [hp]
  exact (specialRelative_unaryRelative T.special r i.succ (Fin.succ_ne_zero i)).symm.trans hq

theorem raw_volume_component_base_preserves_support {b d : ℕ} (h : b=d)
    (X : DefSet (rawVFSpace (M := M) (d+1)) (C.base : Set M)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C d j) (hf : HasRawVolumeComponentSupport hc C X j f) :
    HasRawVolumeComponentSupport hc C (pureVFCoordinateImage X (finCongr (congrArg Nat.succ h))) j
      (aeVolumeFunctionComponentBaseEquiv hc C h j f) := by
  cases h
  change HasRawVolumeComponentSupport hc C (pureVFCoordinateImage X id) j f
  rw [pure_vf_coordinate_image_id]
  exact hf

theorem raw_volume_component_permutation_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) (hf : HasRawVolumeComponentSupport hc C X j f) :
    HasRawVolumeComponentSupport hc C (pureVFCoordinateImage X σ) j
      (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j f) := by
  cases j with
  | succ k => exact raw_positive_permutation_preserves_support hc C X σ f hf
  | zero =>
    obtain ⟨a,F,hF,rfl⟩ := hf
    refine ⟨a,F.permuteBase σ,?_,rfl⟩
    intro q
    have hp := (mem_mixed_vf_permutation_domain F.domain σ q.val.1 q.val.2).mp q.property
    apply (mem_pure_vf_coordinate_image X σ q.val.1).mpr
    exact ⟨q.val.1 ∘ σ.symm,hF ⟨_,hp⟩,funext (fun i => congrArg q.val.1 (σ.symm_apply_apply i))⟩

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_volume_component_head_preserves_support
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C (n+1) j) (hf : HasRawVolumeComponentSupport hc C X j f) :
    HasRawVolumeComponentSupport hc C (pureVFCoordinateImage X Fin.succ) (j+1)
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) := by
  cases j with
  | succ k =>
    obtain ⟨g,rfl⟩ := hf
    exact ⟨supportedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g,
      supported_volume_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g⟩
  | zero =>
    obtain ⟨a,F,hF,rfl⟩ := hf
    let T := ordinaryFamilyHeadPreparation hc Ξ hGenerated F
    refine ⟨Quotient.mk _ ⟨1+T.arity,⟨F.headIntegral hc Ξ T,?_⟩⟩,rfl⟩
    intro q
    obtain ⟨p,hp⟩ := ordinary_head_integral_has_source hc C Ξ F T q
    exact (mem_pure_vf_coordinate_image X Fin.succ q.val.1).mpr ⟨p.val.1,hF p,hp⟩

theorem raw_volume_component_prefix_preserves_support : ∀ (r n j : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M))
    (f : AEVolumeFunctionComponent hc C (n+r) j), HasRawVolumeComponentSupport hc C X j f →
    HasRawVolumeComponentSupport hc C (pureVFPrefixImage r n X) (appendVolumeDegree r j)
      (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n j f) := by
  intro r
  induction r with
  | zero => intro n j X f hf; exact hf
  | succ r ih =>
    intro n j X f hf
    exact ih n (j+1) (pureVFCoordinateImage X Fin.succ) _
      (raw_volume_component_head_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X j f hf)

theorem raw_volume_component_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) (hf : HasRawVolumeComponentSupport hc C X j f) :
    HasRawVolumeComponentSupport hc C (pureVFCoordinateImage X E.retainedIndex) (appendVolumeDegree E.discarded j)
      (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p j
        (aeVolumeFunctionComponentPermutationLinearMap hc C (p+E.discarded) (volumeProjectionFibreOrder E) j
          (aeVolumeFunctionComponentBaseEquiv hc C (volume_projection_index_eq E) j f))) := by
  have hCast := raw_volume_component_base_preserves_support hc C (volume_projection_index_eq E) X j f hf
  have hPerm := raw_volume_component_permutation_preserves_support hc C _ (volumeProjectionFibreOrder E) j _ hCast
  have hPrefix := raw_volume_component_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    E.discarded p j _ _ hPerm
  rw [volume_projection_iterated_image] at hPrefix
  exact hPrefix
end IntegrationInACVF.Section7
