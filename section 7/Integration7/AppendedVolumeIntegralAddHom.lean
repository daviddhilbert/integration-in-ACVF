module

public import Integration7.VolumeCoordinateAdditiveEquivalences
public import Integration7.VolumeFunctionIntegralCoordinateNormalization
public import Integration7.AERVVolumeFunctionIntegralAddHom

@[expose] public section

/-! The actual coefficient-first integral is additive on the AE
function quotient. Its explicit normalization is an additive equivalence,
so additivity follows from the checked canonical integral homomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def canonicalFromAppendedVolumeAddEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ) :
    PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) ≃+
      PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  (positiveVolumeClassPermutationAddEquiv (k := appendVolumeDegree (n+1) k) hc C
    (appendedToOriginalVolumePermutation (n+1) k)).trans
      (positiveVolumeClassDegreeReindexAddEquiv hc C (selected_append_degree_eq n k).symm)

def aeRVVolumeFunctionAppendedIntegralAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n k : ℕ) :
    AERVVolumeFunction hc C n k →+ PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) := by
  let E := canonicalFromAppendedVolumeAddEquiv hc C n k
  let I := aeRVVolumeFunctionIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
  let J := aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n := n) (k := k)
  have hE (f) : E (J f)=I f := ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f
  refine {
    toFun := J
    map_zero' := E.injective ((hE 0).trans (I.map_zero.trans E.map_zero.symm))
    map_add' := ?_ }
  intro f g
  apply E.injective
  calc
    E (J (f+g))=I (f+g) := hE _
    _ = I f+I g := I.map_add _ _
    _ = E (J f)+E (J g) := congrArg₂ (fun x y => x+y) (hE f).symm (hE g).symm
    _ = E (J f+J g) := (E.map_add _ _).symm

end IntegrationInACVF.Section7
