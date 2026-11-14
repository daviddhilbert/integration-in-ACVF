import Integration7.IteratedVolumeBlowups

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VolumeBlowup.transport_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U W) (f : RVVolumeIso U' U) : VolumeBlowup U' W :=
  b.transport hc C f (RVVolumeIso.refl hc C W)

def VolumeBlowup.transport_target
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W W' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U W) (f : RVVolumeIso W' W) : VolumeBlowup U W' :=
  b.transport hc C (RVVolumeIso.refl hc C U) f

theorem IteratedVolumeBlowup.transport_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {n : ℕ}
    (h : IteratedVolumeBlowup n U W) (f : RVVolumeIso U' U) :
    ∃ W', IteratedVolumeBlowup n U' W' ∧ Nonempty (RVVolumeIso W' W) := by
  cases h with
  | refl U => exact ⟨U', .refl U', ⟨f⟩⟩
  | step b rest =>
    exact ⟨W, .step ⟨b.some.transport_source hc C f⟩ rest, ⟨RVVolumeIso.refl hc C W⟩⟩

end IntegrationInACVF.Section7
