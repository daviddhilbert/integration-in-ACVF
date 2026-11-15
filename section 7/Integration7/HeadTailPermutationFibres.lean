import Integration7.VFPermutationMapValues
import IntegrationSection6.HeadTailFibreGeometry

/-! Reordering the frozen tail preserves the actual unary head fibre,
including its available real parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem head_tail_permutation_insert (τ : Equiv.Perm (Fin n)) (u : Fin (n+1) → VF (M := M))
    (p : Point (M := M) 1 a) :
    vfPermutation (headTailPerm τ).symm (coordinateInsert 0 u p) =
      coordinateInsert 0 (u ∘ (headTailPerm τ).symm) p := by
  refine Prod.ext ?_ rfl
  funext j
  cases j using Fin.cases <;>
    simp [vfPermutation,coordinateInsert,headTailPerm_symm,headTailPerm,vfAt,Function.comp_def]

theorem head_tail_permutation_project (τ : Equiv.Perm (Fin n)) (q : Point (M := M) (n+1) a) :
    coordinateProject 0 (vfPermutation (headTailPerm τ) q) = coordinateProject 0 q := by
  refine Prod.ext ?_ rfl
  funext j
  fin_cases j
  rfl

theorem head_tail_permutation_fibre_base (τ : Equiv.Perm (Fin n)) (u : Fin (n+1) → VF (M := M)) :
    coordinateFibreBase S 0 (u ∘ (headTailPerm τ).symm) ⊆ coordinateFibreBase S 0 u := by
  rintro c (hc | ⟨j,rfl⟩)
  · exact Or.inl hc
  · refine Or.inr ⟨⟨(headTailPerm τ).symm j.val,?_⟩,rfl⟩
    intro h
    have hz : (headTailPerm τ).symm 0 = 0 := rfl
    exact j.property ((headTailPerm τ).symm.injective (h.trans hz.symm))

theorem head_tail_permutation_fibre_carrier (A : DefSet (M := M) S (n+1) a)
    (τ : Equiv.Perm (Fin n)) (u : Fin (n+1) → VF (M := M)) :
    carrier (coordinateFibre (vfPermutationImage A (headTailPerm τ)) 0 u) =
      carrier (coordinateFibre A 0 (u ∘ (headTailPerm τ).symm)) := by
  ext p
  change ((coordinateInsert 0 u p).1,(coordinateInsert 0 u p).2) ∈
      carrier (vfPermutationImage A (headTailPerm τ)) ↔
    coordinateInsert 0 (u ∘ (headTailPerm τ).symm) p ∈ carrier A
  rw [vfPermutationImage_row]
  exact Iff.of_eq (congrArg (fun z => z ∈ carrier A) (head_tail_permutation_insert τ u p))

end IntegrationInACVF.Section7
