import Integration7.VolumeCoproduct
import Section5.GammaLift

/-! Normalization preserves the literal RV zero/one tag tuples. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rvLeftTag_normalize (x : Fin a → CanonicalRV.RVSort M) :
    @rvLeftTag M N hN a b x = rvLeftTag b x := by
  funext i
  apply Subtype.ext
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [rvLeftTag,Fin.append_left]
    exact @CanonicalStructure.sortZero_normalize M sM .rv
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [rvLeftTag,rvAppend,Fin.append_right,Fin.append_left]
    · simp only [rvLeftTag,rvAppend,Fin.append_right,rvZeroTuple]
      exact @CanonicalStructure.sortZero_normalize M sM .rv

theorem rvRightTag_normalize (y : Fin b → CanonicalRV.RVSort M) :
    @rvRightTag M N hN b a y = rvRightTag a y := by
  funext i
  apply Subtype.ext
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [rvRightTag,Fin.append_left]
    have h := @CanonicalStructure.normalize_fun M sM 0 Fn.rvOne Fin.elim0 (fun j => j.elim0)
    exact h
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [rvRightTag,rvAppend,Fin.append_right,Fin.append_left,rvZeroTuple]
      exact @CanonicalStructure.sortZero_normalize M sM .rv
    · simp only [rvRightTag,rvAppend,Fin.append_right]

end IntegrationInACVF.Section7
