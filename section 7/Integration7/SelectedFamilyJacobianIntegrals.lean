module

public import Integration7.SelectedFamilyJacobianFullLifts
public import Integration7.VolumeFamilyRealizationIdentifications

@[expose] public section

/-! Literal positive selected-family representatives satisfy change of
variables through their actual full VF realizations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_family_jacobian_canonical_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C (n+1) a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F =
      selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (F.jacobianPushforward φ hφ hF) := by
  have hFull := congrArg (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1)
    ((positiveVFVolumeIsoClass_eq_iff hc C).mpr
      ⟨VFVolumeIso.of_bijection (selectedFamilyJacobianFullLiftBijection hc C (Nat.zero_lt_succ n) F φ hφ hF)⟩)
  exact eq_of_heq ((selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F).trans
    ((heq_of_eq hFull).trans
      (selected_family_canonical_integral_full_lift hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (F.jacobianPushforward φ hφ hF)).symm))

end IntegrationInACVF.Section7
