import Integration7.VFVolumeBijections

/-! Composition and inversion of the actual volume equation on arbitrary
raw mixed domains, before imposing the finite-label object condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem preservesVFVolume_comp
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n a b c : ℕ} (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    (ω : VolumeForm A) (π : VolumeForm B) (ρ : VolumeForm D)
    (f : Map A B) (g : Map B D) (hf : Function.Injective f)
    (hω : PreservesVFVolume ω π f) (hπ : PreservesVFVolume π ρ g) :
    PreservesVFVolume ω ρ (g.comp f) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E, hEA, hd, hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small
    hn f g (Map.finiteFibres_of_injective hf)
  have hchain : VFAlmostEverywhere A (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g.comp f) p (K * J)) := ⟨E, hEA, hd, hE⟩
  have hboth := vfAlmostEverywhere_and hc C hω
    (VFAlmostEverywhere.pullback_injective f hf hπ)
  apply (vfAlmostEverywhere_and hc C hboth hchain).mono
  rintro p ⟨⟨⟨J, hJ, hω⟩, ⟨K, hK, hπ⟩⟩, ⟨J', K', hJ', hK', hcomp⟩⟩
  have heJ := hJ'.unique hJ
  have heK := hK'.unique hK
  subst J'
  subst K'
  refine ⟨K * J, hcomp, ?_⟩
  change ω.value p = ρ.value (g (f p)) * CanonicalRV.encodedRv (K * J)
  rw [RVOperations.rv_mul, hω, hπ, mul_assoc]

theorem preservesVFVolume_inverse
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n a b : ℕ} (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (ω : VolumeForm A) (π : VolumeForm B)
    (f : Map A B) (hf : Function.Bijective f) (hω : PreservesVFVolume ω π f) :
    PreservesVFVolume π ω (f.inverse hf) := by
  let g := f.inverse hf
  have hfg (p : B) : f (g p) = p := Map.apply_inverse _ _ p
  have hgf (p : A) : g (f p) = p := Map.inverse_apply _ _ p
  have hginj : Function.Injective g := by
    intro p q he
    have h := congrArg f he
    simpa only [hfg] using h
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨D, hDB, hd, hD⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small
    hn g f (Map.finiteFibres_of_injective hginj)
  have hchain : VFAlmostEverywhere B (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt g p J ∧ HasMixedVFJacobianAt f (g p) K ∧
      HasMixedVFJacobianAt (f.comp g) p (K * J)) := ⟨D, hDB, hd, hD⟩
  have hid := vfJacobianOne_of_preservesVF hc C hn (f.comp g)
    (fun p => congrArg (fun q : B => q.val.1) (hfg p))
  have hforward := VFAlmostEverywhere.pullback_injective g hginj hω
  apply (vfAlmostEverywhere_and hc C (vfAlmostEverywhere_and hc C hforward hchain) hid).mono
  rintro p ⟨⟨⟨K', hK', hω⟩, ⟨J, K, hJ, hK, hcomp⟩⟩, hId⟩
  have heK := hK.unique hK'
  subst K'
  have hprod : K * J = 1 := hcomp.unique hId
  refine ⟨J, hJ, ?_⟩
  change π.value p = ω.value (g p) * CanonicalRV.encodedRv J
  rw [hω, hfg, mul_assoc, ← RVOperations.rv_mul, hprod, RVOperations.rv_one, mul_one]

end IntegrationInACVF.Section7
