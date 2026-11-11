import IntegrationSection5.VFDifferenceUpdates
import IntegrationSection5.VFPermutation

/-! VF transpositions as three actual relatively-unary definable bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}

theorem vfShear_inverse_val (S : Set M) (m : ℕ) (i j : Fin n) (hij : i ≠ j)
    (q : PresentedSet.univ (pointSpace (M := M) n m) S) :
    (Map.inverse (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij) q).val =
      replace i q.val (vfAt q.val i + vfAt q.val j) := by
  have h : Map.inverse (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij) q =
      ⟨replace i q.val (vfAt q.val i + vfAt q.val j),Set.mem_univ _⟩ := by
    apply (vfDifferenceMap_shear_bijective S m i j hij).1
    rw [Map.apply_inverse]
    exact Subtype.ext (vfDifference_shear_inverse i j hij q.val).symm
  exact congrArg (fun q : PresentedSet.univ (pointSpace (M := M) n m) S => q.val) h

def vfSwapUnaryChain (S : Set M) (m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    UnaryChain S n (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace n m) S) :=
  .cons i (Map.inverse (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij))
    ((Equiv.ofBijective (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij)).symm.bijective)
    (unaryRelative_inverse _ (vfDifferenceMap_shear_bijective S m i j hij)
      (vfDifferenceMap_unary S m i i j))
    (.cons j (vfDifferenceMap S m j i j) (vfDifferenceMap_reflection_bijective S m i j hij)
      (vfDifferenceMap_unary S m j i j)
      (.cons i (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij)
        (vfDifferenceMap_unary S m i i j) (.nil _)))

theorem vfSwapUnaryChain_val (S : Set M) (m : ℕ) (i j : Fin n) (hij : i ≠ j)
    (q : PresentedSet.univ (pointSpace (M := M) n m) S) :
    ((vfSwapUnaryChain S m i j hij).toMap q).val = vfPermutation (Equiv.swap i j) q.val := by
  change vfDifferenceUpdate i i j
    (vfDifferenceUpdate j i j
      (Map.inverse (vfDifferenceMap S m i i j) (vfDifferenceMap_shear_bijective S m i j hij) q).val) = _
  rw [vfShear_inverse_val S m i j hij]
  refine Prod.ext ?_ rfl
  funext k
  by_cases hki : k = i
  · subst k
    simp [vfDifferenceUpdate,replace,vfAt,vfPermutation,hij,Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [vfDifferenceUpdate,replace,vfAt,vfPermutation,hij,Ne.symm hij]
    · simp [vfDifferenceUpdate,replace,vfAt,vfPermutation,hki,hkj,
        Equiv.swap_apply_of_ne_of_ne hki hkj]

end IntegrationInACVF.Section5
