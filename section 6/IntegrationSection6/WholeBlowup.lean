import IntegrationSection6.BlowupPresentations

/-! An elementary blowup is a general blowup at a whole-object locus. -/

noncomputable section

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

def coprodEmptyRightIso (U : RVObject (M := M) S k) :
    U ≅ rvCoprodObject U (RVObject.empty S k) := Classical.choice (by
  apply rvIsoClass_eq_iff.mp
  rw [rvIsoClass_coprod,rvIsoClass_empty,add_zero])

/-- The definition using actual loci includes the original elementary
construction; this is proved through the empty complementary summand. -/
def elementaryWholeBlowup (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    Blowup U (elementary U i) :=
  Blowup.of_split i h (coprodEmptyRightIso U) (coprodEmptyRightIso (elementary U i))

theorem elementary_isp (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    Isp U (elementary U i) := Isp.of_iterated (IteratedBlowup.single (elementaryWholeBlowup U i h))

end IntegrationInACVF.Section6
