module

public import Mathlib.ModelTheory.Definability
public import Mathlib.Basic.Finite.Sum

@[expose] public section

/-!
# Complete-type-generating sets and atomic sets (Definition 3.1)

These definitions use Mathlib's actual first-order definability over a parameter
set. They apply to any language, including an imaginary expansion. They do not
add a new ACVF language or assume that an imaginary expansion has been built.

The paper does not require the set to be nonempty in Definition 3.1. We retain
that convention and state nonemptiness explicitly when selecting a realization.
-/

open Set FirstOrder

namespace IntegrationInACVF.Section3

universe u v w

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]
variable {ι κ : Type*}

/-- Definition 3.1: no set definable over `Q` separates two points of `A`. -/
def GeneratesCompleteType (Q : Set M) (A : Set (ι → M)) : Prop :=
  ∀ B : Set (ι → M), Q.Definable L B → A ⊆ B ∨ Disjoint A B

/-- Definition 3.1: a definable set generating a complete type over the same base. -/
def IsAtomic (Q : Set M) (A : Set (ι → M)) : Prop :=
  Q.Definable L A ∧ GeneratesCompleteType L Q A

variable {L} {Q R : Set M} {A B : Set (ι → M)}

/-- A complete-type-generating set is homogeneous for every definable predicate. -/
theorem GeneratesCompleteType.mem_iff (hA : GeneratesCompleteType L Q A)
    (hB : Q.Definable L B) {a b : ι → M} (ha : a ∈ A) (hb : b ∈ A) :
    a ∈ B ↔ b ∈ B := by
  rcases hA B hB with h | h
  · exact ⟨fun _ => h hb, fun _ => h ha⟩
  · have haB : a ∉ B := fun haB => Set.disjoint_left.mp h ha haB
    have hbB : b ∉ B := fun hbB => Set.disjoint_left.mp h hb hbB
    exact ⟨fun hab => (haB hab).elim, fun hbb => (hbB hbb).elim⟩

/-- Conversely, agreement on definable predicates gives the paper's definition. -/
theorem generatesCompleteType_iff :
    GeneratesCompleteType L Q A ↔
      ∀ B : Set (ι → M), Q.Definable L B →
        ∀ a ∈ A, ∀ b ∈ A, (a ∈ B ↔ b ∈ B) := by
  constructor
  · intro h B hB a ha b hb
    exact h.mem_iff hB ha hb
  · intro h B hB
    by_cases hAB : (A ∩ B).Nonempty
    · obtain ⟨a, ha, haB⟩ := hAB
      exact Or.inl (fun b hb => (h B hB a ha b hb).mp haB)
    · exact Or.inr (Set.disjoint_left.mpr fun a ha haB => hAB ⟨a, ha, haB⟩)

/-- No definability assumption on the smaller set is needed. -/
theorem GeneratesCompleteType.subset (hA : GeneratesCompleteType L Q A)
    (hBA : B ⊆ A) : GeneratesCompleteType L Q B := by
  intro C hC
  rcases hA C hC with h | h
  · exact Or.inl (hBA.trans h)
  · exact Or.inr (Set.disjoint_left.mpr fun b hb hc =>
      Set.disjoint_left.mp h (hBA hb) hc)

/-- Forgetting parameters preserves the complete-type-generating property. -/
theorem GeneratesCompleteType.parameters_mono (hA : GeneratesCompleteType L R A)
    (hQR : Q ⊆ R) : GeneratesCompleteType L Q A :=
  fun B hB => hA B (hB.mono hQR)

/-- A definable part of a complete-type-generating set is empty or the whole set. -/
theorem GeneratesCompleteType.inter_eq (hA : GeneratesCompleteType L Q A)
    (hB : Q.Definable L B) : A ∩ B = ∅ ∨ A ∩ B = A := by
  rcases hA B hB with h | h
  · exact Or.inr (Set.inter_eq_left.mpr h)
  · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mp h)

/-- In particular an atomic set has no proper nonempty definable subset. -/
theorem IsAtomic.eq_of_definable_subset (hA : IsAtomic L Q A)
    (hB : Q.Definable L B) (hBA : B ⊆ A) (hne : B.Nonempty) : B = A := by
  rcases hA.2 B hB with h | h
  · exact Set.Subset.antisymm hBA h
  · obtain ⟨b, hb⟩ := hne
    exact (Set.disjoint_left.mp h (hBA hb) hb).elim

/-- Two atomic sets over one base either coincide or are disjoint. -/
theorem IsAtomic.eq_or_disjoint (hA : IsAtomic L Q A) (hB : IsAtomic L Q B) :
    A = B ∨ Disjoint A B := by
  rcases hA.2 B hB.1 with hAB | hdis
  · rcases hB.2 A hA.1 with hBA | hdis'
    · exact Or.inl (Set.Subset.antisymm hAB hBA)
    · exact Or.inr hdis'.symm
  · exact Or.inr hdis

/-- Definable maps carry complete-type-generating sets to such sets.
This does not assert definability of the source or image. -/
theorem GeneratesCompleteType.image [Finite κ]
    (hA : GeneratesCompleteType L Q A) {f : (ι → M) → (κ → M)}
    (hf : Q.DefinableMap L f) : GeneratesCompleteType L Q (f '' A) := by
  intro C hC
  rcases hA (f ⁻¹' C) (hC.preimage_map hf) with h | h
  · exact Or.inl (by rintro _ ⟨a, ha, rfl⟩; exact h ha)
  · exact Or.inr (Set.disjoint_left.mpr (by
      rintro _ ⟨a, ha, rfl⟩ hfa
      exact Set.disjoint_left.mp h ha hfa))

/-- The image is atomic whenever its definability has also been established. -/
theorem IsAtomic.image_of_definable [Finite κ] (hA : IsAtomic L Q A)
    {f : (ι → M) → (κ → M)} (hf : Q.DefinableMap L f)
    (himage : Q.Definable L (f '' A)) : IsAtomic L Q (f '' A) :=
  ⟨himage, hA.2.image hf⟩

/-- Definability of images follows from the definable graph and projection.
The graph construction follows `Set.Definable.preimage_map` in Mathlib's
`ModelTheory/Definability.lean`; no choice of new parameters is used. -/
theorem definable_image [Finite ι] [Finite κ] (hA : Q.Definable L A)
    {f : (ι → M) → (κ → M)} (hf : Q.DefinableMap L f) :
    Q.Definable L (f '' A) := by
  have hgraph : Q.Definable L
      {z : ι ⊕ κ → M | ∀ i, f (z ∘ Sum.inl) i = z (Sum.inr i)} := by
    rw [Set.ofPred_forall]
    refine Set.definable_iInter_of_finite fun i => ?_
    simpa [Function.tupleGraph, Function.comp_def] using
      (hf i).preimage_comp (fun | none => Sum.inr i | some j => Sum.inl j)
  have hcyl : Q.Definable L {z : ι ⊕ κ → M | z ∘ Sum.inl ∈ A} :=
    hA.preimage_comp Sum.inl
  have hproj := (hgraph.inter hcyl).image_comp (Sum.inr : κ → ι ⊕ κ)
  convert hproj using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Sum.elim x (f x), ⟨fun _ => rfl, hx⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzA⟩, rfl⟩
    exact ⟨z ∘ Sum.inl, hzA, funext hz⟩

/-- Atomic sets have atomic images under definable maps over the same base. -/
theorem IsAtomic.image [Finite ι] [Finite κ] (hA : IsAtomic L Q A)
    {f : (ι → M) → (κ → M)} (hf : Q.DefinableMap L f) :
    IsAtomic L Q (f '' A) :=
  ⟨definable_image hA.1 hf, hA.2.image hf⟩

end IntegrationInACVF.Section3
