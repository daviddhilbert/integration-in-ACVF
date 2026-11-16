import Integration7.HKVolumeClassCoherence
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual volume-isomorphism classes. Only
associativity and distributivity are used; no commutativity is asserted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance rvVolumeIsoClassesGMul (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    GradedMonoid.GMul (RVVolumeIsoClasses hc C) := ⟨fun {n m} => rvVolumeIsoClassesProduct hc C n m⟩

instance rvVolumeIsoClassesGOne (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    GradedMonoid.GOne (RVVolumeIsoClasses hc C) :=
  ⟨rvVolumeIsoClass hc C (n := 0) (unit (C.base : Set M))⟩

instance rvVolumeIsoClassesGMonoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    GradedMonoid.GMonoid (RVVolumeIsoClasses hc C) where
  one_mul a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.zero_add n)
    exact Quotient.inductionOn a (fun U => rvVolumeIsoClass_heq_of_iso hc C (Nat.zero_add n)
      (product _ 0 n (unit (C.base : Set M)) U) U (productLeftUnitIso hc C U))
  mul_one a := by
    obtain ⟨n,a⟩ := a
    apply Sigma.ext (Nat.add_zero n)
    apply heq_of_eq
    exact Quotient.inductionOn a (fun U => Quotient.sound ⟨productRightUnitIso hc C (n := n) U⟩)
  mul_assoc a b c := by
    obtain ⟨n,a⟩ := a
    obtain ⟨m,b⟩ := b
    obtain ⟨l,c⟩ := c
    apply Sigma.ext (Nat.add_assoc n m l)
    exact Quotient.inductionOn₃ a b c (fun U V W => rvVolumeIsoClass_heq_of_iso hc C (Nat.add_assoc n m l)
      (product _ (n+m) l (product _ n m U V) W)
      (product _ n (m+l) U (product _ m l V W)) (productAssocIso hc C U V W))

instance rvVolumeIsoClassesGNonUnitalNonAssocSemiring
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    DirectSum.GNonUnitalNonAssocSemiring (RVVolumeIsoClasses hc C) where
  mul_zero {n m} a := Quotient.inductionOn a (fun U => Quotient.sound
    ⟨productRightZeroIso hc C (n := n) (m := m) U⟩)
  zero_mul {n m} b := Quotient.inductionOn b (fun V => Quotient.sound
    ⟨productLeftZeroIso hc C (n := n) (m := m) V⟩)
  mul_add {n m} a b c := Quotient.inductionOn₃ a b c (fun U V W => Quotient.sound
    ⟨productRightDistribIso hc C (n := n) (m := m) U V W⟩)
  add_mul {n m} a b c := Quotient.inductionOn₃ a b c (fun U V W => Quotient.sound
    ⟨productLeftDistribIso hc C (n := n) (m := m) U V W⟩)

instance rvVolumeIsoClassesGSemiring
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    DirectSum.GSemiring (RVVolumeIsoClasses hc C) where
  natCast n := (n • rvVolumeIsoClass hc C (n := 0) (unit (C.base : Set M)) : RVVolumeIsoClasses hc C 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simp only [succ_nsmul,one_nsmul]
    rfl

abbrev RVVolumeIsoSemiring (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :=
  DirectSum ℕ (RVVolumeIsoClasses hc C)

end IntegrationInACVF.Section7.HK
