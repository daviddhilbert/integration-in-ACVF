import IntegrationSection5.GammaUnaryPartition

/-! Finite gluing of proved unary factorizations on disjoint Gamma pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.GammaUnaryPartition
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m w : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n w)}

theorem glue {ι : Type} [Fintype ι] (e : GammaIso G A B)
    (D : ι → Set (Point (M := M) n m)) (hD : ∀ i, GammaSetDefinable G (D i))
    (hDA : ∀ i, D i ⊆ A) (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hcover : ∀ a : A, ∃ i, a.val ∈ D i)
    (Q : ∀ i, GammaUnaryPartition (gammaRestrictionIso e (D i) (hDA i) (hD i))) :
    Nonempty (GammaUnaryPartition e) := by
  let F := Finset.univ.biUnion (fun i : ι => (Q i).pieces)
  have hmem (E) : E ∈ F ↔ ∃ i : ι, E ∈ (Q i).pieces := by
    simp only [F,Finset.mem_biUnion,Finset.mem_univ,true_and]
  refine ⟨{ pieces := F
            definable := ?_
            subset := ?_
            disjoint := ?_
            cover := ?_
            factors := ?_ }⟩
  · intro E hE
    obtain ⟨i,hi⟩ := (hmem E).mp hE
    exact (Q i).definable E hi
  · intro E hE
    obtain ⟨i,hi⟩ := (hmem E).mp hE
    exact Set.Subset.trans ((Q i).subset E hi) (hDA i)
  · intro E hE H hH hEH
    obtain ⟨i,hi⟩ := (hmem E).mp hE
    obtain ⟨j,hj⟩ := (hmem H).mp hH
    by_cases hij : i = j
    · subst j
      exact (Q i).disjoint E hi H hj hEH
    · exact (hdis i j hij).mono ((Q i).subset E hi) ((Q j).subset H hj)
  · intro a
    obtain ⟨i,hai⟩ := hcover a
    obtain ⟨E,hE,haE⟩ := (Q i).cover ⟨a.val,hai⟩
    exact ⟨E,(hmem E).mpr ⟨i,hE⟩,haE⟩
  · intro E hE
    obtain ⟨i,hi⟩ := (hmem E).mp hE
    obtain ⟨C,T,hT⟩ := (Q i).factors E hi
    refine ⟨C,T,?_⟩
    intro a
    exact hT a

end IntegrationInACVF.Section5.GammaUnaryPartition
