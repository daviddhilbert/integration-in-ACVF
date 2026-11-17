module

public import Integration7.BalancedNativePositionBijections
public import Integration7.BalancedUnaryVolumePreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A balanced native two-cell supplies its actual unary positioning
bijection, both compatible special preparations, and the original-Gamma
comparison of their two product volume objects at any common constant density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M}

set_option maxHeartbeats 2400000 in
theorem balanced_cell_unary_volume_preparation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    (Z : DefSet (M := M) S 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (ε : VF (M := M) → VF (M := M)) (r t : RV (M := M))
    (h : IsBalanced (nativeVFPairDomain Z) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hfΓ : DefinableOverBase P (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hr : r ≠ rv (0 : VF (M := M)))
    (hrS : r.val ∈ S) (htS : t.val ∈ S) (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (η : RV (M := M)) (hηS : η.val ∈ S) (hη0 : η ≠ 0) :
    let A := nativeVFProjectionDomain Z 0
    let B := nativeVFProjectionDomain Z 1
    ∃ S' : Set M, ∃ hSS' : S ⊆ S', ∃ u v : ℕ,
      ∃ A' : DefSet (M := M) S' 1 u, ∃ B' : DefSet (M := M) S' 1 v,
      ∃ TA : SpecialBijection (extendBase A hSS') A', ∃ TB : SpecialBijection (extendBase B hSS') B',
      ∃ hTA : GammaChainDefinable P TA.chain, ∃ hTB : GammaChainDefinable P TB.chain,
      ∃ hA' : IsRVPullback (carrier A'), ∃ hB' : IsRVPullback (carrier B'),
      let hAF := gamma_special_pullback_finite_volume hκ hs hsmall TA hTA hA' (fun _ => Set.toFinite _)
      let hBF := gamma_special_pullback_finite_volume hκ hs hsmall TB hTB hB' (fun _ => Set.toFinite _)
      let U := rvFiniteEssential (canonicalFiniteRVObject hcM ⟨pullbackObject A',hAF⟩)
      let V := rvFiniteEssential (canonicalFiniteRVObject hcM ⟨pullbackObject B',hBF⟩)
      ∃ i : RVVolumeIso
        ((prependFixedRVVolume V r (hSS' hrS) (VolumeForm.one V.obj.domain)).rescale η (hSS' hηS) hη0)
        ((appendFixedRVVolume U t (hSS' htS) (VolumeForm.one U.obj.domain)).rescale η (hSS' hηS) hη0),
        i.GammaDefinable P := by
  intro A B
  let hFib := h.2.2.1
  let f := balancedNativePositionMap Z hFib hf
  exact balanced_unary_volume_preparation hκ hs hsmall h00 γ hγ hγ1 FBase hPS hcM h hr
    hrS htS hr0 ht0 η hηS hη0 A B f (balanced_native_position_bijective Z hFib hf)
    (gamma_native_vf_projection_domain Z 0 hZ) (gamma_native_vf_projection_domain Z 1 hZ)
    (gamma_balanced_native_position_map Z hZ hFib hf hfΓ)
    (fun p => (native_vf_first_projection Z p.val).mp p.property)
    (balanced_native_position_value Z hFib hf)

end IntegrationInACVF.Section7
