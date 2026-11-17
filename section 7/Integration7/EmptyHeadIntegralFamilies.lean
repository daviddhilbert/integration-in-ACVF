module

public import Integration7.AERVVolumeHeadIntegrals
public import Integration7.AERVVolumeFunctionAddition
public import Integration7.IndexedVolumeEmpty

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A head preparation of an empty source has empty contracted domain.
Every empty selected family represents the zero AE function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {C : BaseContext M} {n a k : ℕ}

theorem head_preparation_empty_contracted_domain
    (U : SpecialTransformations.Section5.DefSet (M := M) S (n+1) a)
    (T : HeadPreparation U) (hU : SpecialTransformations.Section5.carrier U = ∅) :
    SpecialTransformations.Section5.carrier T.contractedSet = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨p,hp⟩ := T.contractionMap_surjective ⟨q,hq⟩
  exact hU.le p.property

theorem ae_volume_function_of_empty_family
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C (n+1) a k) (hF : F.domain.carrier = ∅) :
    (Quotient.mk _ ⟨a,F⟩ : AERVVolumeFunction hc C n k) = 0 := by
  apply Quotient.sound
  apply ae_rv_volume_function_equivalent_of_pointwise hc C
  intro x
  have hRow : (F.rowInContext x).underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    exact hF.le hr
  exact positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x)
    (RVVolumeIso.of_empty hc (vfParameterVolumeContext C x) _ _ hRow rfl)

end IntegrationInACVF.Section7
