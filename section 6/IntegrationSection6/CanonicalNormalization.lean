import CanonicalStructure
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
/-! Canonical totalization is idempotent. This lets later bridges retain
the original sorted model while using its actual released presentations. -/
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M]
theorem normalized_structure_eq (h : CanonicalStructure.IsCanonical (M := M)) :
    @CanonicalStructure.normalize M sM = sM := by
  classical
  apply Structure.ext
  · funext n f xs
    change (if ∀ i, sortEval (Fn.argSort f i) (xs i) then
      Structure.funMap f xs else CanonicalStructure.sortZero (Fn.resSort f)) = _
    by_cases ha : ∀ i, sortEval (Fn.argSort f i) (xs i)
    · rw [if_pos ha]
    · rw [if_neg ha, h.1 f xs ha]
  · funext n r xs
    apply propext
    cases r with
    | memVF => rfl
    | memRV => rfl
    | memUnits => rfl
    | rvLe =>
      change ((∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs) ↔ _
      by_cases ha : ∀ i, sortEval .rv (xs i)
      · exact ⟨And.right,fun hr => ⟨ha,hr⟩⟩
      · exact ⟨And.right,fun hr => False.elim (h.2 xs ha hr)⟩

theorem normalized_structure_idempotent :
    @CanonicalStructure.normalize M (@CanonicalStructure.normalize M sM) =
      @CanonicalStructure.normalize M sM :=
  @normalized_structure_eq M (@CanonicalStructure.normalize M sM)
    (@CanonicalStructure.normalize_isCanonical M sM)
end IntegrationInACVF.Section6
