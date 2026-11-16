module

public import Integration7.HeadTailPermutationFibres
public import IntegrationSection5.RelativeFibreMaps

@[expose] public section

/-! Conjugation by a frozen-tail permutation leaves the actual unary
head fibre map unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

theorem head_tail_permutation_fibre_map
    {A : DefSet (M := M) S (n+1) a} {B : DefSet (M := M) S (n+1) b}
    (f : Map A B) (hi : UnaryRelative f 0) (τ : Equiv.Perm (Fin n))
    (u : Fin (n+1) → VF (M := M))
    (p : coordinateFibre (vfPermutationImage A (headTailPerm τ)) 0 u) :
    let hI := vfPermutedMap_relative f (headTailPerm τ) hi
    let q : coordinateFibre A 0 (u ∘ (headTailPerm τ).symm) :=
      ⟨p.val,(Set.ext_iff.mp (head_tail_permutation_fibre_carrier A τ u) p.val).mp p.property⟩
    (coordinateFibreMap (vfPermutedMap f (headTailPerm τ)) 0 hI u p).val =
      (coordinateFibreMap f 0 hi (u ∘ (headTailPerm τ).symm) q).val := by
  intro hI q
  let w : vfPermutationImage A (headTailPerm τ) := ⟨coordinateInsert 0 u p.val,p.property⟩
  let z := Map.inverse (vfPermutationBijection A (headTailPerm τ))
    (vfPermutationBijection_bijective A (headTailPerm τ)) w
  have hz : z = (⟨coordinateInsert 0 (u ∘ (headTailPerm τ).symm) q.val,q.property⟩ : A) := by
    apply Subtype.ext
    exact (vf_permutation_inverse_value A (headTailPerm τ) w).trans (head_tail_permutation_insert τ u p.val)
  change coordinateProject 0 (vfPermutation (headTailPerm τ) (f z).val) =
    coordinateProject 0 (f ⟨coordinateInsert 0 (u ∘ (headTailPerm τ).symm) q.val,q.property⟩).val
  rw [head_tail_permutation_project,hz]

end IntegrationInACVF.Section7
