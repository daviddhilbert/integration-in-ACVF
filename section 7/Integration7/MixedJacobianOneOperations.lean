module

public import Integration7.MixedJacobianVFComparison

@[expose] public section

/-! Jacobian-one maps are closed under injective composition and
bijective inverse on actual raw mixed domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b c : ℕ}

theorem vfJacobianOne_comp
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n c) (C.base : Set M)}
    (f : Map A B) (g : Map B D) (hf : Function.Injective f)
    (hJf : VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1))
    (hJg : VFAlmostEverywhere B (fun p => HasMixedVFJacobianAt g p 1)) :
    VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt (g.comp f) p 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E,hEA,hd,hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn f g
    (Map.finiteFibres_of_injective hf)
  have hchain : VFAlmostEverywhere A (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g.comp f) p (K*J)) := ⟨E,hEA,hd,hE⟩
  have hboth := vfAlmostEverywhere_and hc C hJf (hJg.pullback_injective f hf)
  apply (vfAlmostEverywhere_and hc C hboth hchain).mono
  rintro p ⟨⟨hf,hg⟩,J,K,hJ,hK,hcomp⟩
  have h1 := hJ.unique hf
  have h2 := hK.unique hg
  simpa only [h1,h2,one_mul] using hcomp

theorem vfJacobianOne_inverse
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f)
    (hJf : VFAlmostEverywhere A (fun p => HasMixedVFJacobianAt f p 1)) :
    VFAlmostEverywhere B (fun p => HasMixedVFJacobianAt (f.inverse hf) p 1) := by
  let g := f.inverse hf
  have hfg (p : B) : f (g p) = p := Map.apply_inverse _ _ p
  have hginj : Function.Injective g := by
    intro p q he
    have h := congrArg f he
    simpa only [hfg] using h
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E,hEB,hd,hE⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn g f
    (Map.finiteFibres_of_injective hginj)
  have hchain : VFAlmostEverywhere B (fun p => ∃ J K : VFType (M := M),
      HasMixedVFJacobianAt g p J ∧ HasMixedVFJacobianAt f (g p) K ∧
      HasMixedVFJacobianAt (f.comp g) p (K*J)) := ⟨E,hEB,hd,hE⟩
  have hid := vfJacobianOne_of_preservesVF hc C hn (f.comp g)
    (fun p => congrArg (fun q : B => q.val.1) (hfg p))
  have hforward := hJf.pullback_injective g hginj
  apply (vfAlmostEverywhere_and hc C (vfAlmostEverywhere_and hc C hforward hchain) hid).mono
  rintro p ⟨⟨hf,J,K,hJ,hK,hcomp⟩,hId⟩
  have h1 := hK.unique hf
  have h2 := hcomp.unique hId
  rw [h1,one_mul] at h2
  exact h2 ▸ hJ

end IntegrationInACVF.Section7
