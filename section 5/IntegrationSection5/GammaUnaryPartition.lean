import IntegrationSection5.GammaUnaryPullback

/-! Finite original-Gamma partitions with actual relatively-unary bijection
chains agreeing with the given map on every piece. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m l w : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n w)}

structure GammaUnaryPartition (e : GammaIso G A B) where
  pieces : Finset (Set (Point (M := M) n m))
  definable : ∀ D ∈ pieces, GammaSetDefinable G D
  subset : ∀ D ∈ pieces, D ⊆ A
  disjoint : ∀ D ∈ pieces, ∀ E ∈ pieces, D ≠ E → Disjoint D E
  cover : ∀ a : A, ∃ D ∈ pieces, a.val ∈ D
  factors : ∀ D (hD : D ∈ pieces), ∃ C : Set (Point (M := M) n w),
    ∃ T : GammaUnaryChain G n D C,
      ∀ a : D, (T.toIso.equiv a).val = (e.equiv ⟨a.val,subset D hD a.property⟩).val

namespace GammaUnaryPartition

theorem ofChain (e : GammaIso G A B) (T : GammaUnaryChain G n A B)
    (hT : ∀ a : A, (T.toIso.equiv a).val = (e.equiv a).val) : Nonempty (GammaUnaryPartition e) := by
  refine ⟨{ pieces := {A}
            definable := ?_
            subset := ?_
            disjoint := ?_
            cover := ?_
            factors := ?_ }⟩
  · intro D hD
    have h := Finset.mem_singleton.mp hD
    subst D
    exact (e.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
  · intro D hD
    exact Finset.mem_singleton.mp hD ▸ Set.Subset.refl A
  · intro D hD E hE hne
    exact (hne ((Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hE).symm)).elim
  · intro a
    exact ⟨A,Finset.mem_singleton_self A,a.property⟩
  · intro D hD
    have h := Finset.mem_singleton.mp hD
    subst D
    exact ⟨B,T,hT⟩

theorem ofUnary (e : GammaIso G A B) (i : Fin n)
    (hi : ∀ a : A, ∀ j : Fin n, j ≠ i → (e.equiv a).val.1 j = a.val.1 j) :
    Nonempty (GammaUnaryPartition e) :=
  ofChain e (.cons i e hi (.nil B (e.target_definable (gammaLogicInput G)))) (fun _ => rfl)

theorem prepend {C : Set (Point (M := M) n l)} (e : GammaIso G A B)
    (T : GammaUnaryChain G n A C) (r : GammaIso G C B)
    (hsq : ∀ a : A, (r.equiv (T.toIso.equiv a)).val = (e.equiv a).val)
    (Q : GammaUnaryPartition r) : Nonempty (GammaUnaryPartition e) := by
  let F := Q.pieces.image (gammaIsoPreimage T.toIso)
  refine ⟨{ pieces := F
            definable := ?_
            subset := ?_
            disjoint := ?_
            cover := ?_
            factors := ?_ }⟩
  · intro D hD
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
    exact gammaIsoPreimage_definable T.toIso E (Q.definable E hE)
  · intro D hD
    obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hD
    exact gammaIsoPreimage_subset T.toIso E
  · intro D hD E hE hDE
    obtain ⟨D',hD',rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨E',hE',rfl⟩ := Finset.mem_image.mp hE
    have hne : D' ≠ E' := fun h => hDE (congrArg (gammaIsoPreimage T.toIso) h)
    apply Set.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hba,hbD⟩ := ha
    have hbE := (mem_gammaIsoPreimage T.toIso E' b).mp (hba.symm ▸ hb)
    exact Set.disjoint_left.mp (Q.disjoint D' hD' E' hE' hne) hbD hbE
  · intro a
    obtain ⟨E,hE,haE⟩ := Q.cover (T.toIso.equiv a)
    exact ⟨gammaIsoPreimage T.toIso E,Finset.mem_image.mpr ⟨E,hE,rfl⟩,
      (mem_gammaIsoPreimage T.toIso E a).mpr haE⟩
  · intro D hD
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨V,hV⟩ := T.pullback E (Q.subset E hE) (Q.definable E hE)
    obtain ⟨K,U,hU⟩ := Q.factors E hE
    refine ⟨K,V.append U,?_⟩
    intro a
    have hVa : (⟨(V.toIso.equiv a).val,Q.subset E hE (V.toIso.equiv a).property⟩ : C) =
        T.toIso.equiv ⟨a.val,gammaIsoPreimage_subset T.toIso E a.property⟩ := Subtype.ext (hV a)
    exact (congrArg (fun b : K => b.val) (V.append_apply U a)).trans
      ((hU (V.toIso.equiv a)).trans ((congrArg (fun c : C => (r.equiv c).val) hVa).trans
        (hsq ⟨a.val,gammaIsoPreimage_subset T.toIso E a.property⟩)))

end GammaUnaryPartition
end IntegrationInACVF.Section5
