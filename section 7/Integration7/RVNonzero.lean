import Integration7.VolumeForms

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_nonzero_iff_raw (t : CanonicalRV.RVSort M) : t ≠ 0 ↔ t.val ≠ iRVZero := by
  constructor
  · intro ht hz
    apply ht
    exact Subtype.ext (hz.trans RVOperations.zero_val.symm)
  · intro ht hz
    exact ht ((congrArg Subtype.val hz).trans RVOperations.zero_val)

end IntegrationInACVF.Section7
