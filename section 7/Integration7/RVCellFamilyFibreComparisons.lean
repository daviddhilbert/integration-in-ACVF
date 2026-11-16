module

public import Integration7.NativeTwoCellFibrePresentations
public import Integration7.RVCellFibreNameCertificates
public import Integration7.RVParameterizedCellContractionComparisons

@[expose] public section

/-! The pointwise opposite-order comparison applies to every actual
nonempty labelled fibre of a definable two-cell family. Its native cell
presentation and all tuple/name certificates are constructed internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m : ℕ}

theorem rv_cell_family_fibre_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) S 2 m) (hA : ParameterizedCells.DefinableTwoCell P (carrier A))
    (u : Fin m → RV (M := M)) (hu : (ParameterizedCells.twoFibre (carrier A) u).Nonempty) :
    let C := gammaRVDefinableNamesVolumeContext hc C0 P hP0 hgamma u
    let B := RVLabelSlices.labelBase P u
    let hBC := rv_cell_fibre_real_names hc C0 P hP0 hgamma u
    let hNames := rv_cell_fibre_common_names hc C0 P hP0 hgamma u
    let hz := rv_cell_fibre_tuple_names hc C0 P hP0 hgamma u
    let hzΓ := rv_parameter_tuple_singleton P u
    let Z := nativeTwoCellFibrePresentation A hA u hu hNames
    let hZ := gamma_native_two_cell_fibre_presentation A hA u hu hNames
    ∀ (j : Fin m) (η : RV (M := M)) (hj : u j = η) (hη0 : η ≠ 0)
    (T : StandardContraction (fixedRVLabelDomain Z u hz) (Equiv.refl _))
    (W : StandardContraction (fixedRVLabelDomain Z u hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program),
    let hsmall : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC Z hZ u hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC Z hZ u hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent B (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro C B hBC hNames hz hzΓ Z hZ j η hj hη0 T W hT hW hsmall U V
  exact rv_parameterized_cell_contraction_comparison hc C0 hP0 hBase hgamma γ hγ hγ1 u
    Z hZ (native_two_cell_fibre_presentation_is_cell A hA u hu hNames)
    u hz hzΓ j η hj hη0 T W hT hW

end IntegrationInACVF.Section7
