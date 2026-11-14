import Integration7.VolumeCoproductUnits
import Integration7.VolumeCoproductIsomorphism

/-! Actual positive-degree volume-isomorphism classes. Addition is the
definable coproduct; no blowup relation or scissor quotient is imposed here. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def positiveVolumeIsoSetoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :
    Setoid (PositiveRVVolumeObject (M := M) (C.base : Set M) k) where
  r U V := Nonempty (RVVolumeIso U V)
  iseqv := ⟨fun U => ⟨RVVolumeIso.refl hc C U⟩,
    fun ⟨f⟩ => ⟨f.symm hc C⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans hc C g⟩⟩

abbrev PositiveVolumeIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (k : ℕ) :=
  Quotient (positiveVolumeIsoSetoid hc C k)

def positiveVolumeIsoClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k : ℕ} (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : PositiveVolumeIsoClasses hc C k :=
  Quotient.mk _ U

theorem positiveVolumeIsoClass_eq_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} :
    positiveVolumeIsoClass hc C U = positiveVolumeIsoClass hc C V ↔ Nonempty (RVVolumeIso U V) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := positiveVolumeIsoSetoid hc C k) h⟩

theorem positiveVolumeIsoClass_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (f : RVVolumeIso U V) :
    positiveVolumeIsoClass hc C U = positiveVolumeIsoClass hc C V :=
  Quotient.sound ⟨f⟩

instance positiveVolumeIsoClassesAdd (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (k : ℕ) : Add (PositiveVolumeIsoClasses hc C k) :=
  ⟨Quotient.map₂ PositiveRVVolumeObject.coprod (by
    rintro U U' ⟨f⟩ V V' ⟨g⟩
    exact ⟨f.coprod hc C g⟩)⟩

instance positiveVolumeIsoClassesZero (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (k : ℕ) : Zero (PositiveVolumeIsoClasses hc C k) :=
  ⟨positiveVolumeIsoClass hc C (.empty (C.base : Set M) k)⟩

instance positiveVolumeIsoClassesAddCommMonoid (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (k : ℕ) : AddCommMonoid (PositiveVolumeIsoClasses hc C k) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W => Quotient.sound ⟨volumeCoprodAssoc hc C U V W⟩)
  add_comm a b := Quotient.inductionOn₂ a b (fun U V => Quotient.sound ⟨volumeCoprodSwap hc C U V⟩)
  zero_add a := Quotient.inductionOn a (fun U => Quotient.sound ⟨volumeCoprodLeftUnit hc C U⟩)
  add_zero a := Quotient.inductionOn a (fun U => Quotient.sound ⟨volumeCoprodRightUnit hc C U⟩)
  nsmul := nsmulRec

@[simp] theorem positiveVolumeIsoClass_coprod (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {k : ℕ} (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeIsoClass hc C (U.coprod V) = positiveVolumeIsoClass hc C U + positiveVolumeIsoClass hc C V := rfl

@[simp] theorem positiveVolumeIsoClass_empty (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (k : ℕ) :
    positiveVolumeIsoClass hc C (.empty (C.base : Set M) k) = 0 := rfl

theorem positiveVolumeIsoClass_surjective (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (k : ℕ) : Function.Surjective (positiveVolumeIsoClass hc C (k := k)) := by
  intro a
  exact Quotient.inductionOn a (fun U => ⟨U, rfl⟩)

end IntegrationInACVF.Section7
