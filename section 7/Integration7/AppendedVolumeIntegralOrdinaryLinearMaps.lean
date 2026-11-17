module

public import Integration7.VolumeCoordinateOrdinaryLinearEquivalences
public import Integration7.AppendedVolumeIntegralAddHom
public import Integration7.AERVVolumeOrdinaryLinearIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The coefficient-first AE integral is linear over ordinary RV[0]
coefficients, using the explicit ordinary-linear coordinate normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def canonicalFromAppendedVolumeOrdinaryLinearEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) ≃ₗ[RVVolumeBlowupClasses hc C 0]
      PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  (positiveVolumeClassPermutationOrdinaryLinearEquiv (k := appendVolumeDegree (n+1) k) hc C
    (appendedToOriginalVolumePermutation (n+1) k)).trans
      (positiveVolumeClassDegreeReindexOrdinaryLinearEquiv hc C (selected_append_degree_eq n k).symm)

def aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n k : ℕ) :
    AERVVolumeFunction hc C n k →ₗ[RVVolumeBlowupClasses hc C 0]
      PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) := by
  let E := canonicalFromAppendedVolumeOrdinaryLinearEquiv hc C n k
  let I := aeRVVolumeFunctionIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  let J := aeRVVolumeFunctionAppendedIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  have hE (f) : E (J f)=I f := ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f
  refine { toAddHom := J, map_smul' := ?_ }
  intro z f
  apply E.injective
  calc
    E (J (z • f))=I (z • f) := hE _
    _ = z • I f := I.map_smul _ _
    _ = z • E (J f) := congrArg (fun v => z • v) (hE f).symm
    _ = E (z • J f) := (E.map_smul _ _).symm

end IntegrationInACVF.Section7
