import Integration7.VolumeBlowupAddition
import Integration7.VolumeIsomorphismClasses

/-! The positive-degree common-blowup quotient as an actual additive
commutative monoid, and the quotient homomorphism from isomorphism classes. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev PositiveVolumeBlowupClasses
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :=
  Quotient (muIspSetoid hc C (k + 1))

def positiveVolumeBlowupClass
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    PositiveVolumeBlowupClasses hc C k := Quotient.mk _ U

theorem positiveVolumeBlowupClass_eq_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} :
    positiveVolumeBlowupClass hc C U = positiveVolumeBlowupClass hc C V ↔
      VolumeBlowupEquivalent U V :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := muIspSetoid hc C (k + 1)) h⟩

theorem positiveVolumeBlowupClass_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    positiveVolumeBlowupClass hc C U = positiveVolumeBlowupClass hc C V :=
  Quotient.sound (VolumeBlowupEquivalent.of_iso C e)

instance positiveVolumeBlowupClassesAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Add (PositiveVolumeBlowupClasses hc C k) :=
  ⟨Quotient.map₂ PositiveRVVolumeObject.coprod (by
    intro U U' h V V' g
    exact VolumeBlowupEquivalent.coprod hc C h g)⟩

instance positiveVolumeBlowupClassesZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Zero (PositiveVolumeBlowupClasses hc C k) :=
  ⟨positiveVolumeBlowupClass hc C (.empty (C.base : Set M) k)⟩

instance positiveVolumeBlowupClassesAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    AddCommMonoid (PositiveVolumeBlowupClasses hc C k) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W =>
    positiveVolumeBlowupClass_iso hc C (volumeCoprodAssoc hc C U V W))
  add_comm a b := Quotient.inductionOn₂ a b (fun U V =>
    positiveVolumeBlowupClass_iso hc C (volumeCoprodSwap hc C U V))
  zero_add a := Quotient.inductionOn a (fun U =>
    positiveVolumeBlowupClass_iso hc C (volumeCoprodLeftUnit hc C U))
  add_zero a := Quotient.inductionOn a (fun U =>
    positiveVolumeBlowupClass_iso hc C (volumeCoprodRightUnit hc C U))
  nsmul := nsmulRec

@[simp] theorem positiveVolumeBlowupClass_coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeBlowupClass hc C (U.coprod V) =
      positiveVolumeBlowupClass hc C U + positiveVolumeBlowupClass hc C V := rfl

@[simp] theorem positiveVolumeBlowupClass_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    positiveVolumeBlowupClass hc C (.empty (C.base : Set M) k) = 0 := rfl

theorem positiveVolumeBlowupClass_blowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U V) :
    positiveVolumeBlowupClass hc C U = positiveVolumeBlowupClass hc C V :=
  Quotient.sound (VolumeBlowupEquivalent.of_blowup hc C b)

theorem positiveVolumeBlowupClass_iterated
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k n : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (h : IteratedVolumeBlowup n U V) :
    positiveVolumeBlowupClass hc C U = positiveVolumeBlowupClass hc C V := by
  induction h with
  | refl U => rfl
  | step b h ih =>
    obtain ⟨b⟩ := b
    exact (positiveVolumeBlowupClass_blowup hc C b).trans ih

def positiveVolumeBlowupProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    PositiveVolumeIsoClasses hc C k →+ PositiveVolumeBlowupClasses hc C k where
  toFun := Quotient.lift (positiveVolumeBlowupClass hc C) (by
    rintro U V ⟨e⟩
    exact positiveVolumeBlowupClass_iso hc C e)
  map_zero' := rfl
  map_add' a b := Quotient.inductionOn₂ a b (fun U V => rfl)

@[simp] theorem positiveVolumeBlowupProjection_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeBlowupProjection hc C k (positiveVolumeIsoClass hc C U) =
      positiveVolumeBlowupClass hc C U := rfl

theorem positiveVolumeBlowupProjection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Function.Surjective (positiveVolumeBlowupProjection hc C k) := by
  intro a
  exact Quotient.inductionOn a (fun U => ⟨positiveVolumeIsoClass hc C U, rfl⟩)

end IntegrationInACVF.Section7
