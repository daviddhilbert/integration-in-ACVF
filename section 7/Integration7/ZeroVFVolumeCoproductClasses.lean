module

public import Integration7.ZeroVolumeIntegration
public import Integration7.OrdinaryZeroLiftCoproducts

@[expose] public section

/-! The transported degree-zero coefficient addition is exactly the
actual ordinary VF coproduct, as required for Grothendieck semigroups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_vf_volume_coprod_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : VFVolumeObject (M := M) (C.base : Set M) 0) :
    letI := zeroVFVolumeAddCommMonoid hc C
    zeroVFVolumeIsoClass C
      (vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) A B) =
        zeroVFVolumeIsoClass C A + zeroVFVolumeIsoClass C B := by
  letI := zeroVFVolumeAddCommMonoid hc C
  letI := rvVolumeBlowupClassesAddCommMonoid hc C 0
  let E := zeroVolumeIntegrationAddEquiv hc C
  obtain ⟨U,⟨eA⟩⟩ := ordinary_finite_lift_presentation_exists hc C A
  obtain ⟨V,⟨eB⟩⟩ := ordinary_finite_lift_presentation_exists hc C B
  have hA : E (zeroVFVolumeIsoClass C A) = rvVolumeBlowupClass hc C (n := 0) U :=
    (proposition_7_9_zero hc C A U).mpr (Quotient.sound ⟨eA⟩)
  have hB : E (zeroVFVolumeIsoClass C B) = rvVolumeBlowupClass hc C (n := 0) V :=
    (proposition_7_9_zero hc C B V).mpr (Quotient.sound ⟨eB⟩)
  have hSum := (proposition_7_9_zero hc C
    (vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) A B)
    (rvFiniteCoprodObject U V)).mpr
      (Quotient.sound ⟨(ordinaryFiniteCoprodIso hc C eA eB).trans (ordinaryZeroLiftCoprodIso hc C U V)⟩)
  apply E.injective
  rw [E.map_add,hA,hB]
  exact hSum

end IntegrationInACVF.Section7
