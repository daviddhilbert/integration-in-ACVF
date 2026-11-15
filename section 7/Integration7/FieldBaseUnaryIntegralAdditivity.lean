import Integration7.FieldBaseUnaryIntegralPartitions
import Integration7.VFCoproductLabelCutBijections

/-! Actual unary field-base volume integration preserves coproducts,
including the zero-old-coordinate finite-label case. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem unary_field_volume_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) :
    unaryFieldVolumeIntegral hc C Ξ FBase (U.coprod V) =
      unaryFieldVolumeIntegral hc C Ξ FBase U + unaryFieldVolumeIntegral hc C Ξ FBase V := by
  have hL := unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1
    U _ (vfCoprodLeftCutBijection hc C Ξ hNames U V)
  have hR := unary_field_volume_integral_bijection hc C Ξ hΞ FBase hNames γ hγ hγ1
    V _ (vfCoprodRightCutBijection hc C Ξ hNames U V)
  exact (unary_field_volume_integral_label_partition hc C Ξ hΞ FBase hNames γ hγ hγ1
    (U.coprod V) (fun _ : Fin 1 => (0 : Fin (1+(U.arity+V.arity))))
    (selectedSumLeftTagPredicate hc C) (selected_sum_left_tag_gamma hc C Ξ)
    (selected_sum_right_tag_gamma hc C Ξ)).trans (congrArg₂ (fun x y => x+y) hL.symm hR.symm)
end IntegrationInACVF.Section7
