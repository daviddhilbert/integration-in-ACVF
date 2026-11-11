import IntegrationSection3ACVF.DefinableTupleCompactness

/-! The first compactness step in3.19, for an arbitrary family of allowed
unary parameter definitions. Bad configurations are finite real tuples;
their containment constraints, rather than the type itself, are definable.
The geometric exclusion on a complete type is an explicit input here. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.TypeNeighborhoodCompactness

variable {M : Type} [LRV.Structure M] {n : ℕ}

def core (T : Set (Set M)) (a : M) : Set M :=
  {x | ∀ U ∈ T, a ∈ U → x ∈ U}

theorem exists_neighborhood {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (T : Set (Set M))
    (hInter : ∀ (ι : Type) [Finite ι] (U : ι → T), {x | ∀ i, x ∈ (U i).val} ∈ T)
    (Bad : Set (Fin n → M)) (body : (Fin n → M) → Set M)
    (hDef : ∀ U ∈ T, S.Definable LRV {b | b ∈ Bad ∧ body b ⊆ U})
    (a : M) (hNoBad : ∀ b ∈ Bad, ¬ body b ⊆ core T a) :
    ∃ U ∈ T, a ∈ U ∧ ∀ b ∈ Bad, ¬ body b ⊆ U := by
  classical
  by_contra hn
  have hWitness (U : Set M) (hU : U ∈ T) (haU : a ∈ U) :
      ∃ b ∈ Bad, body b ⊆ U := by
    by_contra he
    exact hn ⟨U,hU,haU,fun b hb hsub => he ⟨b,hb,hsub⟩⟩
  let C : Set (Set (Fin n → M)) :=
    {D | ∃ U ∈ T, a ∈ U ∧ D = {b | b ∈ Bad ∧ body b ⊆ U}}
  have hC : ∀ D ∈ C, S.Definable LRV D := by
    rintro D ⟨U,hU,_,rfl⟩
    exact hDef U hU
  have hFIP : ∀ (ι : Type) [Finite ι] (D : ι → C), ∃ b, ∀ i, b ∈ (D i).val := by
    intro ι _ D
    choose U hU haU hEq using fun i => (D i).property
    let W : Set M := {x | ∀ i, x ∈ U i}
    have hWT : W ∈ T := hInter ι (fun i => ⟨U i,hU i⟩)
    obtain ⟨b,hb,hsub⟩ := hWitness W hWT haU
    refine ⟨b,fun i => ?_⟩
    rw [hEq i]
    exact ⟨hb,fun x hx => hsub hx i⟩
  obtain ⟨b,hb⟩ := DefinableTupleCompactness.realize_fip hs S hsmall C hC hFIP
  have hUniv : Set.univ ∈ T := by
    convert hInter Empty (fun i => Empty.elim i) using 1
    ext x
    simp
  have hbBad : b ∈ Bad :=
    (hb {b | b ∈ Bad ∧ body b ⊆ Set.univ} ⟨Set.univ,hUniv,Set.mem_univ a,rfl⟩).1
  apply hNoBad b hbBad
  intro x hx U hU haU
  exact (hb {b | b ∈ Bad ∧ body b ⊆ U} ⟨U,hU,haU,rfl⟩).2 hx

end IntegrationInACVF.Section3ACVF.TypeNeighborhoodCompactness
