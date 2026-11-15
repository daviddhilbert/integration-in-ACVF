import Integration7.NativeFixedLabelRectangles
import Integration7.NativeUnaryRectangleContractions
import Integration7.NativeUnaryRectangleVolumeCoordinates
import Integration7.FixedLabelsVFPermutations

/-! The constructed rectangle programs give standard contractions of
the same original fixed-label domain in both coordinate orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d r b : ℕ}
variable (D E : DefSet (M := M) S 1 0) (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
variable {D' : DefSet (M := M) S 1 r} {E' : DefSet (M := M) S 1 b}

def fixedNativeRectangleContraction (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    StandardContraction (fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz) (Equiv.refl _) :=
  standardFromProgram _ _ (nativeUnaryRectangleProgram T hD L)
    ((fixed_native_unary_rectangle D E z hz).symm.trans (vfPermutationImage_id_eq _).symm)

theorem gamma_fixed_native_rectangle_contraction (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hT : GammaChainDefinable P T.chain) (hD : IsRVPullback (carrier D'))
    {W : SpecialBijection E E'} (hW : GammaChainDefinable P W.chain)
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    GammaProgramDefinable P (fixedNativeRectangleContraction D E z hz T hD L).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_native_unary_rectangle_program T hT hD hW L)

theorem fixed_native_rectangle_volume_index (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    (fixedNativeRectangleContraction D E z hz T hD L).volumeIndex = (nativeUnaryRectangleProgram T hD L).volumeIndex :=
  orderedCastSource_volumeIndex _ _

theorem swapped_fixed_native_rectangle_source :
    nativeUnaryProductDomain (fixedRVLabelDomain E z hz) D =
      vfPermutationImage (fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz) (Equiv.swap 0 1) :=
  (fixed_native_unary_rectangle E D z hz).symm.trans
    ((congrArg (fun R => fixedRVLabelDomain R z hz) (swapped_native_unary_rectangle D E).symm).trans
      (fixed_rv_label_domain_vf_permutation _ z hz (Equiv.swap 0 1)))

def swappedFixedNativeRectangleContraction (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    StandardContraction (fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz) (Equiv.swap 0 1) :=
  standardFromProgram _ _ (nativeUnaryRectangleProgram T hE L) (swapped_fixed_native_rectangle_source D E z hz)

theorem gamma_swapped_fixed_native_rectangle_contraction (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hT : GammaChainDefinable P T.chain) (hE : IsRVPullback (carrier E'))
    {W : SpecialBijection D D'} (hW : GammaChainDefinable P W.chain)
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    GammaProgramDefinable P (swappedFixedNativeRectangleContraction D E z hz T hE L).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_native_unary_rectangle_program T hT hE hW L)

theorem swapped_fixed_native_rectangle_volume_index (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    (swappedFixedNativeRectangleContraction D E z hz T hE L).volumeIndex =
      (nativeUnaryRectangleProgram T hE L).volumeIndex ∘ Equiv.swap 0 1 := by
  funext i
  change (orderedCastSource _ _).volumeIndex ((Equiv.swap 0 1).symm i) = _
  rw [orderedCastSource_volumeIndex,Equiv.symm_swap]
  rfl

end IntegrationInACVF.Section7
