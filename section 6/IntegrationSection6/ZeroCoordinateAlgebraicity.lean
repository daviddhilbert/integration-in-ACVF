import IntegrationSection6.AlgebraicFibres
import IntegrationSection6.SortedParameterElimination
import Section3.RVGammaAlgebraicity
import Section3.SortedFunctionClosure
import Section3.RVOperations

/-! Zero RV coordinates add no algebraic parameters. This permits the
local simple-root argument to run on the nonzero coordinate stratum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r : ℕ}

theorem algebraicAt_remove_zero_coordinates (f : Fin (r+1) ↪ Fin n) (j : Fin (r+1))
    (t : Fin n → CanonicalRV.RVSort M) (hzero : ∀ i, i ∉ Set.range f → t i = 0)
    {b : M} (hb : AlgebraicAt (coordinateBase S (f j) t) .rv b) :
    AlgebraicAt (S ∪ Set.range (fun i : Fin r => (t (f (j.succAbove i))).val)) .rv b := by
  apply algebraicAt_eliminate_sorted_parameters hb
  intro x hx τ hxτ
  rcases hx with hx | ⟨i,hij,rfl⟩
  · exact (definableClosureAt_of_mem
      (A := S ∪ Set.range (fun i : Fin r => (t (f (j.succAbove i))).val))
      (σ := τ) (x := x) (Or.inl hx) hxτ).algebraic
  · by_cases hi : ∃ l, f l = i
    · obtain ⟨l,rfl⟩ := hi
      have hlj : l ≠ j := fun h => hij (congrArg f h)
      obtain ⟨q,hq⟩ := Fin.exists_succAbove_eq hlj
      exact (definableClosureAt_of_mem
        (A := S ∪ Set.range (fun i : Fin r => (t (f (j.succAbove i))).val))
        (σ := τ) (x := (t (f l)).val) (Or.inr ⟨q,congrArg (fun z => (t (f z)).val) hq⟩) hxτ).algebraic
    · have hz := hzero i hi
      have hτ : τ = .rv := CanonicalStructure.sort_unique hM hxτ (t i).property
      subst τ
      rw [hz,RVOperations.zero_val]
      exact (definableClosureAt_function_symbol _ Fn.rvZero Fin.elim0
        (fun i => i.elim0) (fun i => i.elim0)).algebraic

/-- The same reduction retains every original named Gamma parameter. -/
theorem gammaAlgebraic_remove_zero_coordinates {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (f : Fin (r+1) ↪ Fin n) (j : Fin (r+1)) (t : Fin n → CanonicalRV.RVSort M)
    (hzero : ∀ i, i ∉ Set.range f → t i = 0) {b : M}
    (hb : AlgebraicAtBase ⟨coordinateBase B.real (f j) t,B.gamma⟩ .rv b) :
    AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun i : Fin r => (t (f (j.succAbove i))).val),B.gamma⟩ .rv b := by
  have hsmallOld : Cardinal.mk (coordinateBase B.real (f j) t) < κ := by
    apply (Cardinal.mk_le_mk_of_subset (show coordinateBase B.real (f j) t ⊆
      B.real ∪ Set.range (rvValues t) from ?_)).trans_lt (small_union_range hκ B.real hsmall _)
    rintro x (hx | ⟨i,_,rfl⟩)
    · exact Or.inl hx
    · exact Or.inr (Set.mem_range_self i)
  have hr := (algebraic_rv_gamma_base_iff hκ hs h00
    ⟨coordinateBase B.real (f j) t,B.gamma⟩ hsmallOld b).mp hb
  have he := algebraicAt_remove_zero_coordinates f j t hzero hr
  exact (algebraic_rv_gamma_base_iff hκ hs h00 _
    (small_union_range hκ B.real hsmall _) b).mpr he

end IntegrationInACVF.Section6
