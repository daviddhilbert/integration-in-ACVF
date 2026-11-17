module

public import Integration7.HKZeroVolumeFamilies
public import Integration7.InverseJacobianVolumeForms
public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Change of variables for actual weighted zero-degree family
presentations. The inverse-Jacobian form stays in zero coefficient degree.
This does not yet assert descent to the corrected full AE function module. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b : ℕ}

def ZeroVFVolumeFamily.transport (F : ZeroVFVolumeFamily C n a)
    (B : OrdinaryVFVolumeFamily C n b) (f : Map F.domain B.domain) (hf : Function.Bijective f) :
    ZeroVFVolumeFamily C n b :=
  ⟨B.domain,B.finite_labels,inverseJacobianVFVolumeForm f hf F.form⟩

theorem ZeroVFVolumeFamily.transport_density (F : ZeroVFVolumeFamily C n a)
    (B : OrdinaryVFVolumeFamily C n b) (f : Map F.domain B.domain) (hf : Function.Bijective f) (q : B.domain) :
    (F.transport B f hf).form.value q =
      (mixedJacobianDensityForm (f.inverse hf)).value q * F.form.value (f.inverse hf q) := rfl

def ZeroVFVolumeFamily.transportVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a) (B : OrdinaryVFVolumeFamily C (n+1) b)
    (f : Map F.domain B.domain) (hf : Function.Bijective f) :
    VFVolumeBijection F.fullVFObject (F.transport B f hf).fullVFObject :=
  ⟨f,hf,preserves_inverse_jacobian_vf_volume hc C (Nat.zero_lt_succ n) f hf F.form⟩

theorem ZeroVFVolumeFamily.transport_volume_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : ZeroVFVolumeFamily C (n+1) a) (B : OrdinaryVFVolumeFamily C (n+1) b)
    (f : Map F.domain B.domain) (hf : Function.Bijective f) :
    positiveVFVolumeIsoClass hc C F.fullVFObject =
      positiveVFVolumeIsoClass hc C (F.transport B f hf).fullVFObject :=
  Quotient.sound ⟨VFVolumeIso.of_bijection (F.transportVolumeBijection hc C B f hf)⟩

theorem zero_family_change_of_variables_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : ZeroVFVolumeFamily C (n+1) a) (B : OrdinaryVFVolumeFamily C (n+1) b)
    (f : Map F.domain B.domain) (hf : Function.Bijective f) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C F.fullVFObject) =
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (F.transport B f hf).fullVFObject) :=
  congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
    (F.transport_volume_class hc C B f hf)

end IntegrationInACVF.Section7.HK
