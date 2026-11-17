module

public import Integration7.InverseJacobianVolumeForms
public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual positive VF volume objects satisfy change of variables with
the inverse-Jacobian density, via a genuine volume-preserving bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.inverseJacobianTransport
    (U V : PositiveVFVolumeObject (M := M) S k) (f : Map U.domain V.domain)
    (hf : Function.Bijective f) : PositiveVFVolumeObject (M := M) S k where
  arity := V.arity
  domain := V.domain
  finite_labels := V.finite_labels
  form := inverseJacobianVFVolumeForm f hf U.form

def inverseJacobianVFVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (f : Map U.domain V.domain) (hf : Function.Bijective f) :
    VFVolumeBijection U (U.inverseJacobianTransport V f hf) :=
  ⟨f,hf,preserves_inverse_jacobian_vf_volume hc C (Nat.zero_lt_succ k) f hf U.form⟩

theorem inverse_jacobian_vf_volume_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (f : Map U.domain V.domain) (hf : Function.Bijective f) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C U) =
      positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeIsoClass hc C (U.inverseJacobianTransport V f hf)) :=
  congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
    ((positiveVFVolumeIsoClass_eq_iff hc C).mpr
      ⟨VFVolumeIso.of_bijection (inverseJacobianVFVolumeBijection hc C U V f hf)⟩)

end IntegrationInACVF.Section7
