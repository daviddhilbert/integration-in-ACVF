import Section4.Imported.GrothendieckRing
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The ideal determined by a positive semiring congruence after
Grothendieck completion, with its exact kernel and quotient comparison. -/

noncomputable section

open Algebra

namespace IntegrationInACVF.Section6.GroupifiedCongruence

variable {S : Type*} [CommSemiring S]
local notation "G" => GrothendieckAddGroup
local notation "ι" => GrothendieckAddGroup.ofRingHom

/-- All additive differences of congruent positive representatives. -/
def relationIdeal (c : RingCon S) : Ideal (G S) :=
  Ideal.span {x | ∃ a b : S, c a b ∧ x = ι a - ι b}

def completionMap (c : RingCon S) : G S →+* G c.Quotient :=
  GrothendieckAddGroup.liftRingHom (GrothendieckAddGroup.ofRingHom.comp c.mk')

@[simp] theorem completionMap_of (c : RingCon S) (a : S) :
    completionMap c (ι a) = ι (c.mk' a) :=
  GrothendieckAddGroup.liftRingHom_apply_of _ a

theorem relationIdeal_le_ker (c : RingCon S) : relationIdeal c ≤ RingHom.ker (completionMap c) := by
  rw [relationIdeal,Ideal.span_le]
  rintro x ⟨a,b,hab,rfl⟩
  apply RingHom.mem_ker.mpr
  rw [map_sub,completionMap_of,completionMap_of]
  exact sub_eq_zero.mpr (congrArg (fun q : c.Quotient => ι q) (Quotient.sound hab))

private def positiveEvaluation (c : RingCon S) : c.Quotient →+* (G S ⧸ relationIdeal c) :=
  c.lift ((Ideal.Quotient.mk (relationIdeal c)).comp ι) (by
    intro a b hab
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk (relationIdeal c) (ι a) -
      Ideal.Quotient.mk (relationIdeal c) (ι b) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,b,hab,rfl⟩))

private def evaluation (c : RingCon S) : G c.Quotient →+* (G S ⧸ relationIdeal c) :=
  GrothendieckAddGroup.liftRingHom (positiveEvaluation c)

private theorem evaluation_comp (c : RingCon S) :
    (evaluation c).comp (completionMap c) = Ideal.Quotient.mk (relationIdeal c) := by
  apply GrothendieckAddGroup.ringHom_ext
  intro a
  change evaluation c (completionMap c (ι a)) = _
  rw [completionMap_of]
  exact GrothendieckAddGroup.liftRingHom_apply_of _ (c.mk' a)

/-- This equality includes cancellation newly introduced by groupification. -/
theorem completionMap_kernel (c : RingCon S) :
    RingHom.ker (completionMap c) = relationIdeal c := by
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := DFunLike.congr_fun (evaluation_comp c) x
    rw [RingHom.comp_apply,RingHom.mem_ker.mp hx,map_zero] at he
    exact he.symm
  · exact relationIdeal_le_ker c

theorem completionMap_surjective (c : RingCon S) : Function.Surjective (completionMap c) := by
  intro x
  obtain ⟨a,b,hx⟩ := GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨u,rfl⟩ := c.mk'_surjective a
  obtain ⟨v,rfl⟩ := c.mk'_surjective b
  refine ⟨ι u - ι v,?_⟩
  rw [map_sub,completionMap_of,completionMap_of]
  exact hx.symm

def quotientMap (c : RingCon S) : (G S ⧸ relationIdeal c) →+* G c.Quotient :=
  Ideal.Quotient.lift _ (completionMap c) (fun _ hx =>
    RingHom.mem_ker.mp (relationIdeal_le_ker c hx))

theorem quotientMap_bijective (c : RingCon S) : Function.Bijective (quotientMap c) := by
  constructor
  · exact RingHom.lift_injective_of_ker_le_ideal _ _ (completionMap_kernel c).le
  · intro x
    obtain ⟨a,ha⟩ := completionMap_surjective c x
    exact ⟨Ideal.Quotient.mk (relationIdeal c) a,ha⟩

/-- Groupifying the positive quotient is precisely quotienting the
Grothendieck ring by the ideal of differences of congruent representatives. -/
def quotientEquiv (c : RingCon S) : (G S ⧸ relationIdeal c) ≃+* G c.Quotient :=
  RingEquiv.ofBijective (quotientMap c) (quotientMap_bijective c)

@[simp] theorem quotientEquiv_of (c : RingCon S) (a : S) :
    quotientEquiv c (Ideal.Quotient.mk (relationIdeal c) (ι a)) = ι (c.mk' a) :=
  completionMap_of c a

/-- Generating a semiring congruence introduces no further ideal generators
beyond the differences of its original generating pairs. -/
theorem relationIdeal_generated (r : S → S → Prop) :
    relationIdeal (ringConGen r) = Ideal.span {x | ∃ a b : S, r a b ∧ x = ι a - ι b} := by
  let I : Ideal (G S) := Ideal.span {x | ∃ a b : S, r a b ∧ x = ι a - ι b}
  have hk : ringConGen r ≤ RingCon.ker ((Ideal.Quotient.mk I).comp ι) := by
    apply RingCon.ringConGen_le.mpr
    intro a b hab
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I (ι a) - Ideal.Quotient.mk I (ι b) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,b,hab,rfl⟩)
  apply le_antisymm
  · rw [relationIdeal,Ideal.span_le]
    rintro x ⟨a,b,hab,rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr (hk hab)
  · apply Ideal.span_le.mpr
    rintro x ⟨a,b,hab,rfl⟩
    exact Ideal.subset_span ⟨a,b,RingCon.le_ringConGen _ _ hab,rfl⟩

/-- A single positive generating pair yields a principal groupified ideal. -/
theorem relationIdeal_singleton (u v : S) :
    relationIdeal (ringConGen (fun a b => a = u ∧ b = v)) = Ideal.span {ι u - ι v} := by
  rw [relationIdeal_generated]
  congr 1
  ext x
  constructor
  · rintro ⟨a,b,⟨rfl,rfl⟩,rfl⟩
    exact Set.mem_singleton _
  · intro hx
    exact ⟨u,v,⟨rfl,rfl⟩,Set.mem_singleton_iff.mp hx⟩

end IntegrationInACVF.Section6.GroupifiedCongruence
