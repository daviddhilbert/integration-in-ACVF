import Integration7.VolumeSchemaRowSemantics
import Integration7.PositiveVolumeParameterExtension

/-! Enlarging only the real presentation base retains the exact schema
row interpretation. Coordinate tuples, density values and labels persist. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {B : Base (M := M)} {p k : ℕ}
variable {sp : Fin p → SpecialTransformations.Milestone0.SortTag}

theorem RVVolumeSchemaRow.extend {U : PositiveRVVolumeObject (M := M) S k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}
    (P : RVVolumeSchemaRow U F z) (hST : S ⊆ T) : RVVolumeSchemaRow (U.extend hST) F z := by
  constructor
  · intro x t
    constructor
    · intro h
      obtain ⟨u,hu,hv⟩ := (P.volume_iff x t).mp h
      exact ⟨⟨u.val,u.property⟩,hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact (P.volume_iff x t).mpr ⟨⟨u.val,u.property⟩,hu,hv⟩
  · intro x ω
    constructor
    · intro h
      obtain ⟨u,hu,hv⟩ := (P.density_iff x ω).mp h
      exact ⟨⟨u.val,u.property⟩,hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact (P.density_iff x ω).mpr ⟨⟨u.val,u.property⟩,hu,hv⟩

end IntegrationInACVF.Section7
