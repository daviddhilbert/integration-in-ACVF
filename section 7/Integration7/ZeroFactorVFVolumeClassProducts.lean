import Integration7.ZeroFactorVolumeLiftProducts
import Integration7.PositiveVolumeIntegrationEquivalence
import Integration7.ZeroFactorProductBridges
import Integration7.AllDegreeVolumeClasses

/-! Ordinary degree-zero coefficients act by actual Cartesian product
with their full VF lifts. Integration preserves this geometric action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def positiveVFZeroCoefficientProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (a : PositiveVFVolumeIsoClasses hc C n) (z : RVVolumeBlowupClasses hc C 0) :
    PositiveVFVolumeIsoClasses hc C n :=
  Quotient.map₂ PositiveVFVolumeObject.prod_zero (by
    rintro U V ⟨f⟩ Z T ⟨e⟩
    exact ⟨f.prod_zero hc C e⟩) a z

theorem positive_volume_lift_zero_coefficient_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (a : PositiveVolumeBlowupClasses hc C n) (z : RVVolumeBlowupClasses hc C 0) :
    positiveVolumeLiftOnBlowupClasses hc C n Ξ hGenerated
      (rvVolumeBlowupClassesProduct hc C (n+1) 0 a z) =
      positiveVFZeroCoefficientProduct hc C (positiveVolumeLiftOnBlowupClasses hc C n Ξ hGenerated a) z := by
  induction a using Quotient.inductionOn with
  | h U =>
    induction z using Quotient.inductionOn with
    | h Z =>
      have h := positiveVolumeBlowupClass_iso hc C (volumeProductPositiveZeroIso hc C U Z)
      calc
        _ = positiveVFVolumeIsoClass hc C (rvVolumeLift (U.prod_zero Z)) :=
          congrArg (positiveVolumeLiftOnBlowupClasses hc C n Ξ hGenerated) h
        _ = _ := (positiveVFVolumeIsoClass_eq_iff hc C).mpr
          ⟨(VFVolumeIso.of_bijection (volumeLiftZeroProductBijection hc C U Z)).symm hc C⟩

theorem positive_volume_integration_zero_coefficient_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (a : PositiveVFVolumeIsoClasses hc C n) (z : RVVolumeBlowupClasses hc C 0) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFZeroCoefficientProduct hc C a z) =
      rvVolumeBlowupClassesProduct hc C (n+1) 0
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a) z := by
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := n)
  apply E.symm.injective
  change E.symm (E (positiveVFZeroCoefficientProduct hc C a z)) =
    positiveVolumeLiftOnBlowupClasses hc C n Ξ hGenerated
      (rvVolumeBlowupClassesProduct hc C (n+1) 0 (E a) z)
  rw [E.symm_apply_apply,positive_volume_lift_zero_coefficient_product]
  change positiveVFZeroCoefficientProduct hc C a z = positiveVFZeroCoefficientProduct hc C (E.symm (E a)) z
  rw [E.symm_apply_apply]

end IntegrationInACVF.Section7
