import IntegrationSection6.ProductGeometry
import IntegrationSection6.ProductDistribution
import IntegrationSection6.AdditiveCongruence
import Section4.RVHomogeneousProducts

/-! Multiplicative compatibility of actual common blowups. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k l : ℕ}

/-- A blowup remains an actual blowup after taking a cartesian product. -/
def Blowup.productRight {U V : RVObject (M := M) S k} (h : Blowup U V)
    (R : RVObject (M := M) S l) : Blowup (rvProductObject U R) (rvProductObject V R) := by
  let T := U.restrict (complement U h.locus) (complement_subset U h.locus)
  let es := (rvProductIso h.source_split (Iso.refl R)).trans
    (productLeftDistribIso h.center T R)
  let et := (rvProductIso h.result (Iso.refl R)).trans
    ((productLeftDistribIso (elementary h.center h.coordinate) T R).trans
      (rvCoprodIso (elementaryProductIso h.center R h.coordinate).symm (Iso.refl _)))
  exact Blowup.of_split (Fin.castAdd l h.coordinate) (h.admissible.product R) es et

theorem IteratedBlowup.productRight {U V : RVObject (M := M) S k} {n : ℕ}
    (h : IteratedBlowup n U V) (R : RVObject (M := M) S l) :
    IteratedBlowup n (rvProductObject U R) (rvProductObject V R) := by
  induction h with
  | zero he => exact .zero (he.map (fun e => rvProductIso e (Iso.refl R)))
  | cons h _ ih => exact .cons (h.productRight R) ih

theorem Isp.productRight {U V : RVObject (M := M) S k} (h : Isp U V)
    (R : RVObject (M := M) S l) : Isp (rvProductObject U R) (rvProductObject V R) := by
  obtain ⟨m, n, A, B, hu, hv, he⟩ := h
  exact ⟨m, n, rvProductObject A R, rvProductObject B R,
    hu.productRight R, hv.productRight R, he.map (fun e => rvProductIso e (Iso.refl R))⟩

theorem positiveIsp_cast {a b : RVKPlus (M := M) S k} (h : positiveIsp a b) (e : k = l) :
    positiveIsp (rvKPlusCast e a) (rvKPlusCast e b) := by
  subst l
  exact h

theorem Isp.productLeft {U V : RVObject (M := M) S l} (h : Isp U V)
    (R : RVObject (M := M) S k) : Isp (rvProductObject R U) (rvProductObject R V) := by
  have hp := (positiveIsp_class_iff (rvProductObject U R) (rvProductObject V R)).mpr
    (h.productRight R)
  rw [← rvClassMul_class, ← rvClassMul_class] at hp
  have hc := positiveIsp_cast hp (Nat.add_comm l k)
  rw [rvClassMul_comm_cast, rvClassMul_comm_cast, rvClassMul_class, rvClassMul_class] at hc
  exact (positiveIsp_class_iff _ _).mp hc

theorem Isp.product {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVObject (M := M) S k} {R T : RVObject (M := M) S l}
    (h : Isp U V) (g : Isp R T) : Isp (rvProductObject U R) (rvProductObject V T) :=
  (h.productRight R).trans hκ hs hsmall (g.productLeft V)

/-- The multiplicative compatibility required for the graded version of 6.8. -/
theorem positiveIsp_mul {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {a b : RVKPlus (M := M) S k} {c d : RVKPlus (M := M) S l}
    (h : positiveIsp a b) (g : positiveIsp c d) :
    positiveIsp (rvClassMul a c) (rvClassMul b d) := by
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  obtain ⟨R, rfl⟩ := rvClass_surjective c
  obtain ⟨T, rfl⟩ := rvClass_surjective d
  rw [rvClassMul_class, rvClassMul_class]
  exact (positiveIsp_class_iff _ _).mpr
    (((positiveIsp_class_iff U V).mp h).product hκ hs hsmall
      ((positiveIsp_class_iff R T).mp g))

end IntegrationInACVF.Section6
