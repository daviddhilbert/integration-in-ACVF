module

public import Integration7.PositiveVFVolumeClassProducts
public import Integration7.VolumeLiftProductBijections
public import Integration7.PositiveVolumeIntegrationEquivalence
public import Integration7.AllDegreeVolumeClasses

@[expose] public section

/-! Positive-degree integration preserves the actual Cartesian product,
using the geometric full-lift product bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem positive_volume_lift_on_blowup_classes_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (a : PositiveVolumeBlowupClasses hc C n) (b : PositiveVolumeBlowupClasses hc C m) :
    positiveVolumeLiftOnBlowupClasses hc C ((n+1)+m) Ξ hGenerated
      (rvVolumeBlowupClassesProduct hc C (n+1) (m+1) a b) =
      positiveVFVolumeClassesProduct hc C (positiveVolumeLiftOnBlowupClasses hc C n Ξ hGenerated a)
        (positiveVolumeLiftOnBlowupClasses hc C m Ξ hGenerated b) := by
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V =>
      exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨(volumeLiftProductIso hc C U V).symm hc C⟩

theorem positive_volume_integration_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (a : PositiveVFVolumeIsoClasses hc C n) (b : PositiveVFVolumeIsoClasses hc C m) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (positiveVFVolumeClassesProduct hc C a b) =
      rvVolumeBlowupClassesProduct hc C (n+1) (m+1)
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a)
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 b) := by
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := (n+1)+m)
  let En := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := n)
  let Em := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := m)
  apply E.symm.injective
  change E.symm (E (positiveVFVolumeClassesProduct hc C a b)) =
    positiveVolumeLiftOnBlowupClasses hc C ((n+1)+m) Ξ hGenerated
      (rvVolumeBlowupClassesProduct hc C (n+1) (m+1) (En a) (Em b))
  rw [E.symm_apply_apply,positive_volume_lift_on_blowup_classes_product]
  change positiveVFVolumeClassesProduct hc C a b =
    positiveVFVolumeClassesProduct hc C (En.symm (En a)) (Em.symm (Em b))
  rw [En.symm_apply_apply,Em.symm_apply_apply]

end IntegrationInACVF.Section7
