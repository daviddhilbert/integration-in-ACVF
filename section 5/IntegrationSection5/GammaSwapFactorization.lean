import IntegrationSection5.VFSwapFactorization
import IntegrationSection5.GammaUnaryRestriction

/-! Restricting the actual three-update swap to any original-Gamma source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

theorem gamma_swap_unary_factorization (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (i j : Fin n) :
    ∃ C : Set (Point (M := M) n m), ∃ T : GammaUnaryChain G n A C,
      ∀ a : A, (T.toIso.equiv a).val = vfPermutation (Equiv.swap i j) a.val := by
  by_cases hij : i = j
  · subst j
    refine ⟨A,.nil A hA,?_⟩
    intro a
    change a.val = vfPermutation (Equiv.swap i i) a.val
    exact Prod.ext (funext fun k => by simp [vfPermutation]) rfl
  · obtain ⟨U,hU⟩ := GammaUnaryChain.ofReal (G := G) (vfSwapUnaryChain G.real m i j hij)
    obtain ⟨C,V,_,hV⟩ := U.restrict_exists A (Set.subset_univ _) hA
    refine ⟨C,V,?_⟩
    intro a
    exact (hV a).trans ((hU ⟨a.val,Set.mem_univ _⟩).trans
      (vfSwapUnaryChain_val G.real m i j hij ⟨a.val,Set.mem_univ _⟩))

end IntegrationInACVF.Section5
