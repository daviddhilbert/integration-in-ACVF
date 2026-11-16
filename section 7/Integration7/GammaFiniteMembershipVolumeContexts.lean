module

public import Integration7.VFFieldContainingVolumeContexts
public import IntegrationSection6.GammaFiniteMembershipPreparation
public import IntegrationSection6.GammaSpecialBaseReduction

@[expose] public section

/-! Finite membership preparation over an arbitrary real/Gamma base.
An internal small coefficient-field context supplies the construction;
definable-name elimination keeps its complete special chain over the
original mathematical base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a : ℕ} {ι : Type}

theorem gamma_finite_membership_preparation_in_volume_context
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) n a) (hAP : IsRVPullback (carrier A))
    (hA : GammaSetDefinable P (carrier A))
    (D : ι → DefSet (M := M) (C.base : Set M) n a) (J : Finset ι)
    (hD : ∀ i ∈ J, GammaSetDefinable P (carrier (D i))) :
    ∃ E : BaseContext M, ∃ hCE : (C.base : Set M) ⊆ (E.base : Set M),
    ∃ r : ℕ, ∃ W : DefSet (M := M) (E.base : Set M) n r,
    ∃ T : SpecialBijection (extendBase A hCE) W,
      GammaChainDefinable P T.chain ∧ IsRVPullback (carrier W) ∧
      ∀ i ∈ J, Contractible (Map.comp
        (membershipMap (extendBase A hCE) (extendBase (D i) hCE)) T.inverseMap) := by
  let E := vfFieldContainingVolumeContext C P hPC
  have hCE : (C.base : Set M) ⊆ (E.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C P hPC (Or.inl hx)
  have hPE : (vfFieldNamedBase P).real ⊆ (E.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C P hPC (Or.inr hx)
  let AE := extendBase A hCE
  let DE := fun i => extendBase (D i) hCE
  obtain ⟨r,W,T,hT,hWP,hFlags⟩ := gamma_prepare_finite_membership_all_arity
    (P := vfFieldNamedBase P) E.saturated E.model00
    ((Cardinal.mk_le_mk_of_subset hPE).trans_lt E.small) (vfFieldNamedBase_field P) hPE
    AE hAP (hA.mono Set.subset_union_left (Set.Subset.refl _)) DE J
    (fun i hi => (hD i hi).mono Set.subset_union_left (Set.Subset.refl _))
  exact ⟨E,hCE,r,W,T,(vfFieldBaseReduction P).chainDefinable T.chain hT,hWP,hFlags⟩

end IntegrationInACVF.Section7
