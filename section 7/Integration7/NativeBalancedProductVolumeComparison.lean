import Integration7.BalancedProductStandardVolumeComparison
import Integration7.NativeBalancedProductFibreDomains
import Integration7.BalancedNativePositionBijections

/-! A native balanced cell supplies the actual unary domains and
positioning bijection needed for the constructed opposite-order product
volume comparison. No prepared unary comparison is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}

theorem native_balanced_product_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S) (hc : CanonicalStructure.IsCanonical (M := M))
    (Z : DefSet (M := M) S 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (ε : VF (M := M) → VF (M := M)) (r t : RV (M := M))
    (h : IsBalanced (nativeVFPairDomain Z) ε r t)
    (hf : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hfΓ : DefinableOverBase P (fun _ : Fin 2 => .vf) (positionCodes (first (nativeVFPairDomain Z)) ε))
    (hr : r ≠ rv (0 : VF (M := M))) (hrS : r.val ∈ S) (htS : t.val ∈ S)
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (X Y : DefSet (M := M) S 2 0)
    (hXΓ : GammaSetDefinable P (carrier X)) (hYΓ : GammaSetDefinable P (carrier Y))
    (hX : nativeVFPairDomain X = {x | rv x = r} ×ˢ second (nativeVFPairDomain Z))
    (hY : nativeVFPairDomain Y = first (nativeVFPairDomain Z) ×ˢ {x | rv x = t})
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    ∃ F : TwoOrderProductPreparations X Y (nativeVFProjectionDomain Z 0) (nativeVFProjectionDomain Z 1)
      r t z hz P,
    ∃ i : RVVolumeIso (F.headVolumeObject hκ hs hsmall hc hrS η hη hη0)
      (F.tailVolumeObject hκ hs hsmall hc htS η hη hη0), i.GammaDefinable P := by
  let hFib := h.2.2.1
  let f := balancedNativePositionMap Z hFib hf
  exact balanced_product_standard_volume_comparison hκ hs hsmall h00 γ hγ hγ1 FBase hPS hc h hr
    hrS htS hr0 ht0 (nativeVFProjectionDomain Z 0) (nativeVFProjectionDomain Z 1)
    f (balanced_native_position_bijective Z hFib hf)
    (gamma_native_vf_projection_domain Z 0 hZ) (gamma_native_vf_projection_domain Z 1 hZ)
    (gamma_balanced_native_position_map Z hZ hFib hf hfΓ)
    (fun p => (native_vf_first_projection Z p.val).mp p.property)
    (balanced_native_position_value Z hFib hf) X Y hXΓ hYΓ
    (native_rv_class_product_fibre_condition X Z r hX)
    (native_product_rv_class_swapped_fibre_condition Y Z t hY) z hz hzΓ η hη hη0

end IntegrationInACVF.Section7
