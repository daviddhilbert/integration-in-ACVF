import Mathlib.RingTheory.FreeRing
import Mathlib.RingTheory.Congruence.Hom

/-! The universal ring obtained from a possibly noncommutative semiring.
This reconstructs a missing prerequisite of the recovered Section 7 sources.
It imposes the semiring laws on the generators of a free ring, without
assuming cancellation or commutativity of multiplication. -/

noncomputable section

namespace IntegrationInACVF.Section7

universe u v w

inductive SemiringGroupificationRelation (R : Type u) [Semiring R] :
    FreeRing R → FreeRing R → Prop
  | zero : SemiringGroupificationRelation R (FreeRing.of 0) 0
  | one : SemiringGroupificationRelation R (FreeRing.of 1) 1
  | add (a b : R) :
      SemiringGroupificationRelation R (FreeRing.of (a + b))
        (FreeRing.of a + FreeRing.of b)
  | mul (a b : R) :
      SemiringGroupificationRelation R (FreeRing.of (a * b))
        (FreeRing.of a * FreeRing.of b)

def semiringGroupificationCongruence (R : Type u) [Semiring R] : RingCon (FreeRing R) :=
  ringConGen (SemiringGroupificationRelation R)

abbrev SemiringGroupification (R : Type u) [Semiring R] :=
  (semiringGroupificationCongruence R).Quotient

def semiringGroupificationOf (R : Type u) [Semiring R] : R →+* SemiringGroupification R where
  toFun a := (semiringGroupificationCongruence R).mk' (FreeRing.of a)
  map_zero' := (semiringGroupificationCongruence R).eq.mpr
    (RingCon.le_ringConGen _ _ (SemiringGroupificationRelation.zero))
  map_one' := (semiringGroupificationCongruence R).eq.mpr
    (RingCon.le_ringConGen _ _ (SemiringGroupificationRelation.one))
  map_add' a b := (semiringGroupificationCongruence R).eq.mpr
    (RingCon.le_ringConGen _ _ (SemiringGroupificationRelation.add a b))
  map_mul' a b := (semiringGroupificationCongruence R).eq.mpr
    (RingCon.le_ringConGen _ _ (SemiringGroupificationRelation.mul a b))

theorem semiringGroupification_lift_compatible {R : Type u} [Semiring R]
    {T : Type v} [Ring T] (f : R →+* T) :
    semiringGroupificationCongruence R ≤ RingCon.ker (FreeRing.lift f) := by
  apply RingCon.ringConGen_le.mpr
  intro x y h
  change FreeRing.lift f x = FreeRing.lift f y
  cases h <;> simp

def semiringGroupificationLift {R : Type u} [Semiring R] {T : Type v} [Ring T]
    (f : R →+* T) : SemiringGroupification R →+* T :=
  (semiringGroupificationCongruence R).lift (FreeRing.lift f)
    (semiringGroupification_lift_compatible f)

@[simp] theorem semiringGroupificationLift_of {R : Type u} [Semiring R]
    {T : Type v} [Ring T] (f : R →+* T) (a : R) :
    semiringGroupificationLift f (semiringGroupificationOf R a) = f a :=
  FreeRing.lift_of f a

@[ext] theorem semiringGroupification_hom_ext {R : Type u} [Semiring R]
    {T : Type v} [Ring T] {f g : SemiringGroupification R →+* T}
    (h : ∀ a, f (semiringGroupificationOf R a) = g (semiringGroupificationOf R a)) : f = g := by
  have he : f.comp (semiringGroupificationCongruence R).mk' =
      g.comp (semiringGroupificationCongruence R).mk' := FreeRing.hom_ext h
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := (semiringGroupificationCongruence R).mk'_surjective z
  exact DFunLike.congr_fun he x

def semiringGroupificationMap {R : Type u} [Semiring R] {T : Type v} [Semiring T]
    (f : R →+* T) : SemiringGroupification R →+* SemiringGroupification T :=
  semiringGroupificationLift ((semiringGroupificationOf T).comp f)

@[simp] theorem semiringGroupificationMap_of {R : Type u} [Semiring R]
    {T : Type v} [Semiring T] (f : R →+* T) (a : R) :
    semiringGroupificationMap f (semiringGroupificationOf R a) =
      semiringGroupificationOf T (f a) := semiringGroupificationLift_of _ _

@[simp] theorem semiringGroupificationMap_id (R : Type u) [Semiring R] :
    semiringGroupificationMap (RingHom.id R) = RingHom.id (SemiringGroupification R) := by
  apply semiringGroupification_hom_ext
  intro a
  simp

@[simp] theorem semiringGroupificationMap_comp {R : Type u} [Semiring R]
    {T : Type v} [Semiring T] {U : Type w} [Semiring U]
    (f : R →+* T) (g : T →+* U) :
    semiringGroupificationMap (g.comp f) =
      (semiringGroupificationMap g).comp (semiringGroupificationMap f) := by
  apply semiringGroupification_hom_ext
  intro a
  simp

end IntegrationInACVF.Section7
