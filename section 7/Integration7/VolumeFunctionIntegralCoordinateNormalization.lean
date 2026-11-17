module

public import Integration7.AppendedVolumeFunctionIntegrals
public import Integration7.VolumeClassCoordinatePermutations
public import Integration7.VolumeClassDegreeReindexing
public import Integration7.SelectedIntegralNormalizationIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The exact coordinate identification between coefficient-first
and VF-first family integrals. Normalization consists only of the fixed
RV coordinate permutation and the arithmetic total-degree reindexing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def canonicalFromAppendedVolumeClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) → PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  fun x => positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k).symm
    (positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C (appendedToOriginalVolumePermutation (n+1) k) x)

theorem selected_family_appended_canonical_coordinate_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C
        (appendedToOriginalVolumePermutation (n+1) k) (selectedFamilyIntegralValue hc C Ξ hGenerated F) =
      positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k)
        (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F) :=
  positiveVolumeBlowupClass_iso hc C
    (selectedIntegralNormalizationIso hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
      F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected
      (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)))

theorem ae_rv_volume_integral_coordinate_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C n k) :
    positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C (appendedToOriginalVolumePermutation (n+1) k)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) =
      positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k)
        (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F => exact selected_family_appended_canonical_coordinate_formula hc C Ξ hGenerated F.2

theorem ae_rv_volume_integral_from_appended
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C n k) :
    canonicalFromAppendedVolumeClass hc C n k
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) =
      aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  unfold canonicalFromAppendedVolumeClass
  rw [ae_rv_volume_integral_coordinate_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact (positiveVolumeClassDegreeReindexEquiv hc C (selected_append_degree_eq n k)).left_inv _

end IntegrationInACVF.Section7
