module

public import Integration7.NonbalancedCellContractionComparisons
public import Integration7.GammaNamesGenericParameters

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The arbitrary specified nonbalanced-cell comparison in the common-name
context of the original Gamma base, with preservation of VF independence
proved internally and no VF coefficient-field hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}

theorem gamma_named_nonbalanced_cell_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C0 : BaseContext M)
    (hP0 : P.real ⊆ (C0.base : Set M)) (hBase : P.real = (C0.base : Set M))
    (hgamma : Cardinal.mk P.gamma < C0.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ) :
    let C := gammaNamesContainingVolumeContext C0 P hP0 hgamma
    let hPC : P.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_names_containing_volume_context_contains C0 P hP0 hgamma (Or.inl (hP0 hx))
    ∀ (Z : DefSet (M := M) (C.base : Set M) 2 0) (hZ : GammaSetDefinable P (carrier Z))
    (f : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hCell : CellData (nativeVFPairDomain Z) f t) (ht : t ≠ rv (0 : VF (M := M)))
    (hNot : ¬ ∃ u, IsBalanced (nativeVFPairDomain Z) f u t)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    (T : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.refl _))
    (W : StandardContraction (fixedRVLabelDomain Z z hz) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable P T.program) (hW : GammaProgramDefinable P W.program),
    let hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
    let U := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 T hT
    let V := fixedLabelContractionGammaObject C.uncountable.le C.saturated hsmall hc C hPC Z hZ z hz hzΓ j η hj hη0 W hW
    ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
      GammaVolumeBlowupEquivalent P (K.base : Set M) 1 (U.extend hCK) (V.extend hCK) := by
  intro C hPC Z hZ f t hCell ht hNot z hz hzΓ j η hj hη0 T W hT hW
  have hNames : commonRealNames P ⊆ (C.base : Set M) := fun _ hx =>
    gamma_names_containing_volume_context_contains C0 P hP0 hgamma (Or.inr hx)
  have hη : η.val ∈ (C.base : Set M) := by rw [← hj];exact hz j
  exact nonbalanced_cell_contraction_comparison hc C hgamma γ hγ hγ1 hPC hNames
    (fun x hx => gamma_names_context_preserves_independence hc C0 P hP0 hgamma hBase x hx)
    Z hZ f t hCell ht hNot z hz hzΓ j η hj hη hη0 T W hT hW

end IntegrationInACVF.Section7
