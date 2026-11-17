module

public import Integration7.PositiveVolumeLiftInjectivity
public import Integration7.PositiveVolumeLiftSurjectivity
public import Integration7.VolumeLiftCoproductBijections
public import Integration7.FixedVFVolumeCoproductIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The canonical positive-degree additive integration equivalence is
the inverse of the actual lift. Addition on VF classes is actual coproduct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

instance positiveVFVolumeIsoClassesAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Add (PositiveVFVolumeIsoClasses hc C k) :=
  ⟨Quotient.map₂ PositiveVFVolumeObject.coprod (by
    rintro U U' ⟨f⟩ V V' ⟨g⟩
    exact ⟨f.coprod hc C g⟩)⟩

theorem positive_volume_lift_on_blowup_classes_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (a b : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated (a+b) =
      positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated a +
        positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated b := by
  induction a using Quotient.inductionOn with
  | h U =>
    induction b using Quotient.inductionOn with
    | h V =>
      exact (positiveVFVolumeIsoClass_eq_iff hc C).mpr ⟨(volumeLiftCoprodIso hc C U V).symm hc C⟩

def positiveVolumeIntegrationEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    PositiveVFVolumeIsoClasses hc C k ≃+ PositiveVolumeBlowupClasses hc C k :=
  (AddEquiv.mk' (Equiv.ofBijective (positiveVolumeLiftOnBlowupClasses hc C k Ξ hGenerated)
    ⟨positive_volume_lift_on_blowup_classes_injective hc C Ξ hΞ hGenerated hNames γ hγ hγ1,
      positive_volume_lift_on_blowup_classes_surjective hc C Ξ hGenerated⟩)
    (positive_volume_lift_on_blowup_classes_add hc C Ξ hGenerated)).symm

theorem proposition_7_9_positive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (positiveVFVolumeIsoClass hc C A) =
      positiveVolumeBlowupClass hc C U ↔
      positiveVFVolumeIsoClass hc C A = positiveVFVolumeIsoClass hc C (rvVolumeLift U) := by
  exact (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).toEquiv.eq_symm_apply.symm

end IntegrationInACVF.Section7
