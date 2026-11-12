import IntegrationSection6.FiniteBlowups
import IntegrationSection6.GradedIsp
import Section4.RVFiniteGradedSemiring

/-! Restrict the actual congruences to finite-volume scissors. Preservation
of all blowup witnesses was proved in FiniteBlowups. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

def finiteIspAddCon {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    AddCon (RVFiniteKPlus (M := M) S k) :=
  AddCon.comap rvFiniteForgetKPlus (map_add rvFiniteForgetKPlus) (ispAddCon hκ hs hsmall)

theorem finiteIspAddCon_class_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U V : RVFiniteObject (M := M) S k) :
    finiteIspAddCon hκ hs hsmall (rvFiniteClass U) (rvFiniteClass V) ↔ finiteIsp U V := by
  change positiveIsp (rvFiniteForgetKPlus (rvFiniteClass U))
    (rvFiniteForgetKPlus (rvFiniteClass V)) ↔ _
  rw [rvFiniteForgetKPlus_class, rvFiniteForgetKPlus_class]
  exact positiveIsp_class_iff U.obj V.obj

def finiteIspRingCon {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    RingCon (RVFiniteGradedKPlus (M := M) S) :=
  (ispRingCon hκ hs hsmall).comap rvFiniteGradedForgetSemiring

theorem finiteIspRingCon_class_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U V : RVFiniteObject (M := M) S k) :
    finiteIspRingCon hκ hs hsmall (rvFiniteGradedClass U) (rvFiniteGradedClass V) ↔
      finiteIsp U V := by
  change ispRingCon hκ hs hsmall
    (rvFiniteGradedForgetSemiring (rvFiniteGradedClass U))
    (rvFiniteGradedForgetSemiring (rvFiniteGradedClass V)) ↔ _
  change ispRingCon hκ hs hsmall
    (rvFiniteGradedForget (rvFiniteGradedClass U))
    (rvFiniteGradedForget (rvFiniteGradedClass V)) ↔ _
  simp only [rvFiniteGradedClass, rvFiniteGradedForget, DirectSum.map_of,
    rvFiniteForgetKPlus_class]
  exact ispRingCon_class_iff hκ hs hsmall U.obj V.obj

end IntegrationInACVF.Section6
