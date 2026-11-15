import Integration7.FixedNativeRectangleContractions
import Integration7.FixedLabelUnarySpecialPreparations
import Integration7.UnaryPullbackCommonNamePreparations

/-! Actual preparations for both orders of a rectangle, built in the
same prescribed common-name context. The first stage carries every old
fixed label; the second stage carries the entire first contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}

structure TwoOrderRectanglePreparations (D E : DefSet (M := M) S 1 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) (P : Base (M := M)) where
  dArity : ℕ
  eArity : ℕ
  dTarget : DefSet (M := M) S 1 dArity
  eTarget : DefSet (M := M) S 1 eArity
  dSpecial : SpecialBijection D dTarget
  eSpecial : SpecialBijection E eTarget
  dGamma : GammaChainDefinable P dSpecial.chain
  eGamma : GammaChainDefinable P eSpecial.chain
  dPullback : IsRVPullback (carrier dTarget)
  ePullback : IsRVPullback (carrier eTarget)
  dFixed : ConstantRVLabelSpecialPreparation dSpecial (fixedRVLabelDomain D z hz) (Fin.append Fin.elim0 z) P
  eFixed : ConstantRVLabelSpecialPreparation eSpecial (fixedRVLabelDomain E z hz) (Fin.append Fin.elim0 z) P
  headTail : RVParameterSpecialPreparation eSpecial
    (headImage (nativeUnaryProductDomain dFixed.target E)) (headImage dFixed.target) P
  tailTail : RVParameterSpecialPreparation dSpecial
    (headImage (nativeUnaryProductDomain eFixed.target D)) (headImage eFixed.target) P

theorem gamma_two_order_rectangle_preparations_exists
    (C : BaseContext M) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (D E : DefSet (M := M) (C.base : Set M) 1 0)
    (hD : GammaSetDefinable P (carrier D)) (hE : GammaSetDefinable P (carrier E))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    Nonempty (TwoOrderRectanglePreparations D E z hz P) := by
  obtain ⟨r,D',TD,hTD,hD'⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1 D hD
  obtain ⟨b,E',TE,hTE,hE'⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1 E hE
  obtain ⟨LD⟩ := gamma_fixed_label_unary_special_preparation_exists TD hTD hD' z hz hzΓ
  obtain ⟨LE⟩ := gamma_fixed_label_unary_special_preparation_exists TE hTE hE' z hz hzΓ
  obtain ⟨LH⟩ := gamma_native_rectangle_tail_preparation_exists LD.special LD.gamma TE hTE hE'
  obtain ⟨LT⟩ := gamma_native_rectangle_tail_preparation_exists LE.special LE.gamma TD hTD hD'
  exact ⟨⟨r,b,D',E',TD,TE,hTD,hTE,hD',hE',LD,LE,LH,LT⟩⟩

namespace TwoOrderRectanglePreparations
variable {D E : DefSet (M := M) S 1 0} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

def headContraction (F : TwoOrderRectanglePreparations D E z hz P) :=
  fixedNativeRectangleContraction D E z hz F.dFixed.special F.dFixed.pullback F.headTail

def tailContraction (F : TwoOrderRectanglePreparations D E z hz P) :=
  swappedFixedNativeRectangleContraction D E z hz F.eFixed.special F.eFixed.pullback F.tailTail

theorem head_contraction_gamma (F : TwoOrderRectanglePreparations D E z hz P) :
    GammaProgramDefinable P F.headContraction.program :=
  gamma_fixed_native_rectangle_contraction D E z hz F.dFixed.special F.dFixed.gamma F.dFixed.pullback F.eGamma F.headTail

theorem tail_contraction_gamma (F : TwoOrderRectanglePreparations D E z hz P) :
    GammaProgramDefinable P F.tailContraction.program :=
  gamma_swapped_fixed_native_rectangle_contraction D E z hz F.eFixed.special F.eFixed.gamma F.eFixed.pullback F.dGamma F.tailTail

end TwoOrderRectanglePreparations
end IntegrationInACVF.Section7
