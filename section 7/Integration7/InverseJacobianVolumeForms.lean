module

public import Integration7.VFVolumeDensityTransport

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The paper's inverse-Jacobian density is an actual nonzero definable
form. The definable Jacobian is set to one on its exceptional zero locus;
the inverse and forward densities satisfy the exact product law almost everywhere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

def inverseJacobianVFVolumeForm
    {A : DefSet (rawMixedSpace (M := M) n a) S} {B : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) : VolumeForm B :=
  (mixedJacobianDensityForm (f.inverse hf)).mul (ω.pullback (f.inverse hf))

theorem inverse_jacobian_vf_volume_form_value
    {A : DefSet (rawMixedSpace (M := M) n a) S} {B : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) (q : B) :
    (inverseJacobianVFVolumeForm f hf ω).value q =
      (mixedJacobianDensityForm (f.inverse hf)).value q * ω.value (f.inverse hf q) := rfl

theorem mixed_inverse_jacobian_density_balance_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f) :
    VFAlmostEverywhere A (fun p =>
      (mixedJacobianDensityForm (f.inverse hf)).value (f p) * (mixedJacobianDensityForm f).value p = 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  let g := f.inverse hf
  have hg : Function.Bijective g := by
    constructor
    · intro u v h
      exact (Map.apply_inverse f hf u).symm.trans ((congrArg f h).trans (Map.apply_inverse f hf v))
    · intro p
      exact ⟨f p,Map.inverse_apply f hf p⟩
  obtain ⟨D,hDA,hd,hD⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn f g
    (Map.finiteFibres_of_injective hf.1)
  have hChain : VFAlmostEverywhere A (fun p => ∃ J K : VFType (M := M),
    HasMixedVFJacobianAt f p J ∧ HasMixedVFJacobianAt g (f p) K ∧
      HasMixedVFJacobianAt (g.comp f) p (K*J)) := ⟨D,hDA,hd,hD⟩
  have hId := vfJacobianOne_of_preservesVF hc C hn (g.comp f)
    (fun p => congrArg (fun q : A => q.val.1) (Map.inverse_apply f hf p))
  have hF := mixed_bijective_jacobian_density_ae hc C hn f hf
  have hG := VFAlmostEverywhere.pullback_injective f hf.1
    (mixed_bijective_jacobian_density_ae hc C hn g hg)
  apply (vfAlmostEverywhere_and hc C (vfAlmostEverywhere_and hc C hChain hId)
    (vfAlmostEverywhere_and hc C hF hG)).mono
  rintro p ⟨⟨⟨J,K,hJ,hK,hComp⟩,hOne⟩,⟨⟨J',hJ',hJ0,hJF⟩,⟨K',hK',hK0,hKG⟩⟩⟩
  have heJ := hJ.unique hJ'
  have heK := hK.unique hK'
  have hProd : K*J = 1 := hComp.unique hOne
  rw [hJF,hKG,← heJ,← heK,← RVOperations.rv_mul,hProd,RVOperations.rv_one]

theorem preserves_inverse_jacobian_vf_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f) (ω : VolumeForm A) :
    PreservesVFVolume ω (inverseJacobianVFVolumeForm f hf ω) f := by
  apply (vfAlmostEverywhere_and hc C (mixed_bijective_jacobian_density_ae hc C hn f hf)
    (mixed_inverse_jacobian_density_balance_ae hc C hn f hf)).mono
  rintro p ⟨⟨J,hJ,hJ0,hValue⟩,hBalance⟩
  refine ⟨J,hJ,?_⟩
  change ω.value p = ((mixedJacobianDensityForm (f.inverse hf)).value (f p) *
    ω.value (f.inverse hf (f p))) * CanonicalRV.encodedRv J
  rw [Map.inverse_apply,← hValue]
  calc
    ω.value p = ω.value p * 1 := (mul_one _).symm
    _ = ω.value p * ((mixedJacobianDensityForm (f.inverse hf)).value (f p) *
        (mixedJacobianDensityForm f).value p) := congrArg (fun t => ω.value p * t) hBalance.symm
    _ = _ := by ac_rfl

end IntegrationInACVF.Section7
