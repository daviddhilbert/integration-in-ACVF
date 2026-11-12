import Section4.RVCategories
import Section4.RVCoordinates
import Section3.SmallFiniteParameters

/-!
# Algebraic label fibres for elementary blowups

The dependence condition in Definition 6.1 is model-theoretic algebraicity
over the actual base together with the other label coordinates. Genuine
saturation converts this pointwise condition into finite label fibres.
This is the finiteness input in Remark 6.2; no finiteness of the underlying
RV object is assumed.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] {S : Set M} {k : ℕ}

/-- The base and all label coordinates except the chosen coordinate. -/
def coordinateBase (S : Set M) (i : Fin k) (t : Fin k → CanonicalRV.RVSort M) : Set M :=
  S ∪ {x | ∃ j : Fin k, j ≠ i ∧ (t j).val = x}

/-- The nonzero and algebraicity requirements of Definition 6.1. -/
structure Admissible (U : RVObject (M := M) S k) (i : Fin k) : Prop where
  nonzero : ∀ a : U.domain, (U.value a i).val ≠ iRVZero
  algebraic : ∀ a : U.domain,
    AlgebraicAt (coordinateBase S i (U.value a)) .rv (U.value a i).val

/-- Fix the unmodified coordinates. The chosen coordinate remains free. -/
def coordinateSlice (A : DefSet (rawRVSpace (M := M) k) S) (i : Fin k)
    (t : Fin k → CanonicalRV.RVSort M) :
    DefSet (rawRVSpace (M := M) k) (S ∪ Set.range (rvValues t)) where
  carrier := {r | r ∈ A.carrier ∧ ∀ j, j ≠ i → r j = t j}
  definable := by
    let T := S ∪ Set.range (rvValues t)
    have hA := A.definable.mono (rawRVSpace k) (Set.subset_union_left : S ⊆ T)
    have he (j : {j : Fin k // j ≠ i}) :
        T.Definable LRV {z : Fin k → M | z j.val = (t j.val).val} :=
      (Set.DefinableFun.proj LRV).ofPred_eq
        (LRV.definableFun_const (Fin k) (Or.inr (Set.mem_range_self j.val)))
    have hall := Set.definable_iInter_of_finite he
    change T.Definable LRV _
    have hraw : T.Definable LRV ((rawRVSpace (M := M) k).preimage A.carrier) := hA
    convert hraw.inter hall using 1
    ext z
    constructor
    · rintro ⟨hz, hr, hm⟩
      refine ⟨⟨hz, hr⟩, Set.mem_iInter.mpr ?_⟩
      intro j
      exact (congrFun (rvValues_decode ⟨z, hz⟩) j.val).symm.trans
        (congrArg Subtype.val (hm j.val j.property))
    · rintro ⟨⟨hz, hr⟩, hm⟩
      refine ⟨hz, hr, ?_⟩
      intro j hj
      apply Subtype.ext
      exact (congrFun (rvValues_decode ⟨z, hz⟩) j).trans
        (Set.mem_iInter.mp hm ⟨j, hj⟩)

/-- Algebraicity over fixed other coordinates gives a finite actual set
of label tuples. The parameter bound includes the fixed tuple. -/
theorem coordinateSlice_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawRVSpace (M := M) k) S) (i : Fin k)
    (ha : ∀ a : A, AlgebraicAt (coordinateBase S i a.val) .rv (a.val i).val)
    (t : Fin k → CanonicalRV.RVSort M) : (coordinateSlice A i t).carrier.Finite := by
  apply finite_rv_set_of_algebraic hs (small_union_range hκ S hsmall (rvValues t))
  intro r j
  by_cases hj : j = i
  · subst j
    apply (ha ⟨r.val, r.property.1⟩).mono
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨j, congrArg Subtype.val (r.property.2 j hj).symm⟩
  · rw [r.property.2 j hj]
    exact (definableClosureAt_of_mem (A := S ∪ Set.range (rvValues t)) (σ := .rv)
      (x := (t j).val) (Or.inr ⟨j,rfl⟩) (t j).property).algebraic

/-- The finite old labels over any fixed tuple of unchanged labels.
This is used for both the projection morphism and finite-volume preservation. -/
theorem Admissible.finite_label_fibres {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U : RVObject (M := M) S k} {i : Fin k} (h : Admissible U i)
    (t : Fin k → CanonicalRV.RVSort M) :
    {r | (∃ a : U.domain, U.value a = r) ∧ ∀ j, j ≠ i → r j = t j}.Finite := by
  apply coordinateSlice_finite hκ hs hsmall U.volume.image i ?_ t
  rintro ⟨r, a, rfl⟩
  exact h.algebraic a

end IntegrationInACVF.Section6
