import IntegrationSection6.FocusRootDomains
import Section3.CanonicalParameters

/-! Whole-fibre root validity is unchanged by the released normalization:
its field guards exclude every wrong-sort application. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] {n : ℕ}

theorem rawTupleFibre_normalize (t : Fin n → M) :
    @rawTupleFibre M (@CanonicalStructure.normalize M sM) n t = rawTupleFibre t := by
  ext a
  apply forall_congr'
  intro i
  change (iVF (a i) ∧ @iRv M (@CanonicalStructure.normalize M sM) (a i) = t i) ↔
    (iVF (a i) ∧ iRv (a i) = t i)
  apply and_congr_right
  intro ha
  have he := @CanonicalStructure.normalize_fun M sM 1 Fn.rvMap ![a i]
    (by intro j; fin_cases j; exact ha)
  change @iRv M (@CanonicalStructure.normalize M sM) (a i) = iRv (a i) at he
  rw [he]

theorem rootDomain_normalize (R : Set (Fin n → M)) (j : Fin n) :
    @rootDomain M (@CanonicalStructure.normalize M sM) n R j = rootDomain R j := by
  ext t
  simp only [rootDomain,Set.mem_setOf_eq,rawTupleFibre_normalize]

end IntegrationInACVF.Section6
