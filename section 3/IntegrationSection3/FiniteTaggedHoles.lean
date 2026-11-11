module

public import IntegrationSection3.TaggedLineMaps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Exact component and total-hole counts for finite scalar-tagged
families of cofinite lines. Tags are actual distinct field elements. -/

open Set Classical
open scoped BigOperators

namespace IntegrationInACVF.Section3.FiniteTaggedHoles

variable {K ι : Type*} [Fintype ι]

noncomputable def tags (e : ι ↪ K) : Finset K := by
  classical
  exact Finset.univ.image e

noncomputable def holes (e : ι ↪ K) (F : ι → Finset K) : Finset (Fin 2 → K) := by
  classical
  exact Finset.univ.biUnion (fun i => (F i).image (fun t => ![t,e i]))

theorem tags_card (e : ι ↪ K) : (tags e).card = Fintype.card ι := by
  classical
  exact (Finset.card_image_of_injective _ e.injective).trans (Finset.card_univ)

theorem mem_holes (e : ι ↪ K) (F : ι → Finset K) (i : ι) (t : K) :
    (![t,e i] : Fin 2 → K) ∈ holes e F ↔ t ∈ F i := by
  classical
  constructor
  · intro ht
    obtain ⟨j,_,hs⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hs
    have hj : j = i := e.injective (by simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun heq 1)
    have hu' : u = t := congrFun heq 0
    simpa only [hj,hu'] using hu
  · intro ht
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩

theorem holes_subset (e : ι ↪ K) (F : ι → Finset K) :
    (holes e F : Set (Fin 2 → K)) ⊆ TaggedLineMaps.space (tags e) := by
  classical
  intro x hx
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem holes_card (e : ι ↪ K) (F : ι → Finset K) :
    (holes e F).card = ∑ i, (F i).card := by
  classical
  have hDis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (F i).image (fun t => (![t,e i] : Fin 2 → K))) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hxi
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hxj
    apply hij
    apply e.injective
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun (ht.trans hs.symm) 1
  rw [holes,Finset.card_biUnion hDis]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.card_image_of_injective _ (fun t u he => congrFun he 0)

theorem cofinite_mem (e : ι ↪ K) (F : ι → Finset K) (x : Fin 2 → K) :
    x ∈ TaggedLineMaps.space (tags e) \ holes e F ↔ ∃ i, x 1 = e i ∧ x 0 ∉ F i := by
  classical
  constructor
  · rintro ⟨hx,hNot⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    have he : x = ![x 0,e i] := by
      funext k
      fin_cases k
      · rfl
      · exact hi.symm
    refine ⟨i,hi.symm,?_⟩
    intro ht
    exact hNot (he.symm ▸ (mem_holes e F i (x 0)).mpr ht)
  · rintro ⟨i,hi,hNot⟩
    have he : x = ![x 0,e i] := by
      funext k
      fin_cases k
      · rfl
      · exact hi
    refine ⟨?_,?_⟩
    · change x 1 ∈ tags e
      exact hi.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    · intro hx
      exact hNot ((mem_holes e F i (x 0)).mp (he ▸ hx))

end IntegrationInACVF.Section3.FiniteTaggedHoles
