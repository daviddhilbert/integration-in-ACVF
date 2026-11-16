import Integration7.HKJacobianComponentRepresentatives
import Integration7.HKAEVolumeComponentHeadIntegrals
import Integration7.RawHomogeneousCoordinateSupports

/-! Genuine homogeneous supports survive coordinate Jacobians and
one-coordinate integration. The zero component uses its supplied form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev HasVolumeComponentSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) : Prop :=
  ∃ g : SupportedVolumeFunctionComponent hc C X j, supportedVolumeComponentForgetAddHom hc C X j g = f

theorem zero_head_integral_has_source
    (Ξ : Set (Values.Gamma (M := M))) (F : ZeroVFVolumeFamily C (n+1) a)
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

theorem volume_component_coordinate_jacobian_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) (hf : HasVolumeComponentSupport hc C X j f) :
    HasVolumeComponentSupport hc C (pureVFCoordinateImage X σ) j
      (aeVolumeComponentJacobianAddHom hc C (pureVFPermutationMap (DefSet.univ _ _) σ)
        (pure_vf_univ_permutation_bijective C σ) j f) := by
  obtain ⟨g,rfl⟩ := hf
  cases j with
  | zero =>
    induction g using Quotient.inductionOn with
    | h F =>
      change HasVolumeComponentSupport hc C _ 0
        (aeVolumeComponentJacobianAddHom hc C _ _ 0 (Quotient.mk _ ⟨F.1,F.2.val⟩))
      rw [ae_zero_volume_component_jacobian_representative]
      refine ⟨Quotient.mk _ ⟨F.1,⟨_,?_⟩⟩,rfl⟩
      rintro ⟨q,p,hp⟩
      have he := congrArg Prod.fst hp
      change p.val.1 ∘ σ=q.1 at he
      exact (mem_pure_vf_coordinate_image X σ q.1).mpr ⟨p.val.1,F.2.property p,he⟩
  | succ k =>
    induction g using Quotient.inductionOn with
    | h F =>
      change HasVolumeComponentSupport hc C _ (k+1)
        (aeVolumeComponentJacobianAddHom hc C _ _ (k+1) (Quotient.mk _ ⟨F.1,F.2.val⟩))
      rw [ae_positive_volume_component_jacobian_representative]
      refine ⟨Quotient.mk _ ⟨F.1,⟨_,?_⟩⟩,rfl⟩
      rintro ⟨q,p,hp⟩
      have he := congrArg Prod.fst hp
      change p.val.1 ∘ σ=q.1 at he
      exact (mem_pure_vf_coordinate_image X σ q.1).mpr ⟨p.val.1,F.2.property p,he⟩

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem volume_component_head_preserves_support
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) (j : ℕ)
    (f : AEVolumeFunctionComponent hc C (n+1) j) (hf : HasVolumeComponentSupport hc C X j f) :
    HasVolumeComponentSupport hc C (pureVFCoordinateImage X Fin.succ) (j+1)
      (aeVolumeFunctionComponentHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f) := by
  obtain ⟨g,rfl⟩ := hf
  cases j with
  | succ k =>
    exact ⟨supportedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g,
      supported_volume_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g⟩
  | zero =>
    induction g using Quotient.inductionOn with
    | h F =>
      let T := zeroFamilyHeadPreparation hc Ξ hGenerated F.2.val
      refine ⟨Quotient.mk _ ⟨1+T.arity,⟨F.2.val.headIntegral hc Ξ T,?_⟩⟩,rfl⟩
      intro q
      obtain ⟨p,hp⟩ := zero_head_integral_has_source hc C Ξ F.2.val T q
      exact (mem_pure_vf_coordinate_image X Fin.succ q.val.1).mpr ⟨p.val.1,F.2.property p,hp⟩

end IntegrationInACVF.Section7.HK
