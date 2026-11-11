import CanonicalStructure

/-! A canonical LRV interpretation is already equal to its totalization.
This is equality of the whole language structure, not an identification
of residue quotients belonging to different structures. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

namespace IntegrationInACVF.Section3ACVF.CanonicalModelEquality

variable {M : Type} [sM : LRV.Structure M]

theorem normalize_eq (hc : CanonicalStructure.IsCanonical (M := M)) :
    CanonicalStructure.normalize (M := M) = sM := by
  apply FirstOrder.Language.Structure.ext
  · funext n f xs
    by_cases hs : ∀ i, sortEval (Fn.argSort f i) (xs i)
    · exact CanonicalStructure.normalize_fun f xs hs
    · exact (if_neg hs).trans (hc.1 f xs hs).symm
  · funext n r xs
    apply propext
    cases r with
    | memVF => rfl
    | memRV => rfl
    | memUnits => rfl
    | rvLe =>
      change ((∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs) ↔ _
      refine ⟨And.right,fun hr => ⟨?_,hr⟩⟩
      by_contra hs
      exact hc.2 xs hs hr

end IntegrationInACVF.Section3ACVF.CanonicalModelEquality
