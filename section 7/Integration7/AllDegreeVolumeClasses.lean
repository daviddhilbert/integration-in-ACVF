import Integration7.AllDegreeVolumeCoproducts
import Integration7.AllDegreeVolumeBlowupProducts

/-! Actual isomorphism and common-blowup quotient classes in all degrees.
Addition is coproduct and the graded product descends from the proved
geometric congruence; semiring coherence is not assumed as an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeIsoSetoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Setoid (RVVolumeObject (M := M) (C.base : Set M) n) where
  r U V := Nonempty (RVVolumeIsoInDegree (C.base : Set M) n U V)
  iseqv := by
    cases n with
    | zero => exact ⟨fun U => ⟨Iso.refl U⟩,fun ⟨f⟩ => ⟨f.symm⟩,fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩
    | succ k => exact (positiveVolumeIsoSetoid hc C k).iseqv

abbrev RVVolumeIsoClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  Quotient (rvVolumeIsoSetoid hc C n)

abbrev RVVolumeBlowupClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :=
  Quotient (muIspSetoid hc C n)

def rvVolumeIsoClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) : RVVolumeIsoClasses hc C n := Quotient.mk _ U

def rvVolumeBlowupClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) : RVVolumeBlowupClasses hc C n := Quotient.mk _ U

theorem rvVolumeIsoClass_eq_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n} :
    rvVolumeIsoClass hc C U = rvVolumeIsoClass hc C V ↔
      Nonempty (RVVolumeIsoInDegree (C.base : Set M) n U V) :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound (s := rvVolumeIsoSetoid hc C n) h⟩

theorem rvVolumeBlowupClass_eq_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n} :
    rvVolumeBlowupClass hc C U = rvVolumeBlowupClass hc C V ↔ MuIsp (C.base : Set M) n U V :=
  ⟨fun h => Quotient.exact h,fun h => Quotient.sound (s := muIspSetoid hc C n) h⟩

theorem muIsp_of_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n}
    (f : RVVolumeIsoInDegree (C.base : Set M) n U V) : MuIsp (C.base : Set M) n U V := by
  cases n with
  | zero => exact ⟨f⟩
  | succ k => exact VolumeBlowupEquivalent.of_iso C f

instance rvVolumeIsoClassesAdd (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Add (RVVolumeIsoClasses hc C n) :=
  ⟨Quotient.map₂ (rvVolumeCoprod (C.base : Set M) n) (by
    rintro U U' ⟨f⟩ V V' ⟨g⟩
    exact ⟨rvVolumeCoprodIso hc C (n := n) (U := U) (U' := U') (V := V) (V' := V') f g⟩)⟩

instance rvVolumeIsoClassesZero (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Zero (RVVolumeIsoClasses hc C n) := ⟨rvVolumeIsoClass hc C (rvVolumeEmpty (C.base : Set M) n)⟩

instance rvVolumeIsoClassesAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AddCommMonoid (RVVolumeIsoClasses hc C n) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W =>
    Quotient.sound ⟨rvVolumeCoprodAssocIso hc C (n := n) U V W⟩)
  add_comm a b := Quotient.inductionOn₂ a b (fun U V =>
    Quotient.sound ⟨rvVolumeCoprodSwapIso hc C (n := n) U V⟩)
  add_zero a := Quotient.inductionOn a (fun U => Quotient.sound ⟨rvVolumeCoprodRightUnitIso hc C (n := n) U⟩)
  zero_add a := Quotient.inductionOn a (fun U => Quotient.sound ⟨rvVolumeCoprodLeftUnitIso hc C (n := n) U⟩)
  nsmul := nsmulRec

instance rvVolumeBlowupClassesAdd
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Add (RVVolumeBlowupClasses hc C n) :=
  ⟨Quotient.map₂ (rvVolumeCoprod (C.base : Set M) n) (by
    intro U U' h V V' g
    exact muIsp_coprod hc C (n := n) (U := U) (U' := U') (V := V) (V' := V') h g)⟩

instance rvVolumeBlowupClassesZero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Zero (RVVolumeBlowupClasses hc C n) := ⟨rvVolumeBlowupClass hc C (rvVolumeEmpty (C.base : Set M) n)⟩

instance rvVolumeBlowupClassesAddCommMonoid
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    AddCommMonoid (RVVolumeBlowupClasses hc C n) where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun U V W => Quotient.sound
    (muIsp_of_iso hc C (n := n) (U := _) (V := _) (rvVolumeCoprodAssocIso hc C (n := n) U V W)))
  add_comm a b := Quotient.inductionOn₂ a b (fun U V => Quotient.sound
    (muIsp_of_iso hc C (n := n) (U := _) (V := _) (rvVolumeCoprodSwapIso hc C (n := n) U V)))
  add_zero a := Quotient.inductionOn a (fun U => Quotient.sound
    (muIsp_of_iso hc C (n := n) (U := _) (V := _) (rvVolumeCoprodRightUnitIso hc C (n := n) U)))
  zero_add a := Quotient.inductionOn a (fun U => Quotient.sound
    (muIsp_of_iso hc C (n := n) (U := _) (V := _) (rvVolumeCoprodLeftUnitIso hc C (n := n) U)))
  nsmul := nsmulRec

def rvVolumeIsoClassesProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n m : ℕ) :
    RVVolumeIsoClasses hc C n → RVVolumeIsoClasses hc C m → RVVolumeIsoClasses hc C (n+m) :=
  Quotient.map₂ (rvVolumeProduct (C.base : Set M) n m) (by
    rintro U U' ⟨f⟩ V V' ⟨g⟩
    exact ⟨rvVolumeProductIso hc C (n := n) (m := m) (U := U) (U' := U') (V := V) (V' := V') f g⟩)

def rvVolumeBlowupClassesProduct
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n m : ℕ) :
    RVVolumeBlowupClasses hc C n → RVVolumeBlowupClasses hc C m → RVVolumeBlowupClasses hc C (n+m) :=
  Quotient.map₂ (rvVolumeProduct (C.base : Set M) n m) (by
    intro U U' h V V' g
    exact muIsp_product hc C (n := n) (m := m) (U := U) (U' := U') (V := V) (V' := V') h g)

def rvVolumeBlowupProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    RVVolumeIsoClasses hc C n →+ RVVolumeBlowupClasses hc C n where
  toFun := Quotient.lift (rvVolumeBlowupClass hc C) (by
    rintro U V ⟨f⟩
    exact Quotient.sound (muIsp_of_iso hc C (n := n) (U := U) (V := V) f))
  map_zero' := rfl
  map_add' a b := Quotient.inductionOn₂ a b (fun U V => rfl)

theorem rvVolumeBlowupProjection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Function.Surjective (rvVolumeBlowupProjection hc C n) := by
  intro a
  exact Quotient.inductionOn a (fun U => ⟨rvVolumeIsoClass hc C U,rfl⟩)

theorem rvVolumeBlowupProjection_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n m : ℕ)
    (a : RVVolumeIsoClasses hc C n) (b : RVVolumeIsoClasses hc C m) :
    rvVolumeBlowupProjection hc C (n+m) (rvVolumeIsoClassesProduct hc C n m a b) =
      rvVolumeBlowupClassesProduct hc C n m (rvVolumeBlowupProjection hc C n a)
        (rvVolumeBlowupProjection hc C m b) :=
  Quotient.inductionOn₂ a b (fun U V => rfl)

end IntegrationInACVF.Section7
