import IntegrationSection6.ProductCongruence
import IntegrationSection6.GradedCongruence
import Section4.RVGradedSemiring

/-! Lemma 6.8 on the actual graded positive RV scissors. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M}

def gradedIsp (a b : RVGradedKPlus (M := M) S) : Prop :=
  ∀ k, positiveIsp (a k) (b k)

/-- The componentwise common-blowup relation respects addition and
multiplication of genuine graded scissors. -/
def ispRingCon {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    RingCon (RVGradedKPlus (M := M) S) :=
  GradedCongruence.congruence (fun _ => ispAddCon hκ hs hsmall)
    (fun h g => positiveIsp_mul hκ hs hsmall h g)

theorem ispRingCon_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (a b : RVGradedKPlus (M := M) S) :
    ispRingCon hκ hs hsmall a b ↔ gradedIsp a b :=
  GradedCongruence.congruence_iff _ _ a b

theorem ispRingCon_class_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) {k : ℕ}
    (U V : RVObject (M := M) S k) :
    ispRingCon hκ hs hsmall (rvGradedClass U) (rvGradedClass V) ↔ Isp U V :=
  (GradedCongruence.congruence_of_iff _ _ k (rvClass U) (rvClass V)).trans
    (positiveIsp_class_iff U V)

end IntegrationInACVF.Section6
