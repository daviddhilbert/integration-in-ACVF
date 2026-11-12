import IntegrationSection6.GammaUnivPresentations

/-! Finite unions of actual mixed Gamma sets, on a common internal
presentation. The original real/Gamma base is unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ} {ι : Type}

def mixedFiniteUnionSet (D : ι → DefSet (M := M) Set.univ n a) (F : Finset ι) : Set (Point (M := M) n a) :=
  {p | ∃ i ∈ F, p ∈ carrier (D i)}

theorem mixedFiniteUnionSet_empty (D : ι → DefSet (M := M) Set.univ n a) : mixedFiniteUnionSet D ∅ = ∅ := by
  ext p
  simp [mixedFiniteUnionSet]

theorem mixedFiniteUnionSet_insert (D : ι → DefSet (M := M) Set.univ n a) (i : ι) (F : Finset ι) :
    mixedFiniteUnionSet D (insert i F) = carrier (D i) ∪ mixedFiniteUnionSet D F := by
  ext p
  constructor
  · rintro ⟨j,hj,hp⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hp
    · exact Or.inr ⟨j,hj,hp⟩
  · rintro (hp | ⟨j,hj,hp⟩)
    · exact ⟨i,Finset.mem_insert_self _ _,hp⟩
    · exact ⟨j,Finset.mem_insert_of_mem hj,hp⟩

theorem gamma_mixedFiniteUnionSet (D : ι → DefSet (M := M) Set.univ n a)
    (hD : ∀ i, GammaSetDefinable B (carrier (D i))) (F : Finset ι) :
    GammaSetDefinable B (mixedFiniteUnionSet D F) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [mixedFiniteUnionSet_empty]
    let E := @SpecialTransformations.DefinableGeometry.DefSet.empty LRV M
      (@CanonicalStructure.normalize M sM) (pointSpace n a) B.real
    exact (gammaLogicInput B).real_set (carrier E) (setDefinable E)
  | insert i F hi ih =>
    rw [mixedFiniteUnionSet_insert]
    exact (gammaLogicInput B).union (hD i) ih

def gammaMixedFiniteUnion (D : ι → DefSet (M := M) Set.univ n a)
    (hD : ∀ i, GammaSetDefinable B (carrier (D i))) (F : Finset ι) : DefSet (M := M) Set.univ n a :=
  gammaDefSetUniv (mixedFiniteUnionSet D F) (gamma_mixedFiniteUnionSet D hD F)

theorem mixedFiniteUnion_subset {U : DefSet (M := M) Set.univ n a}
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, carrier (D i) ⊆ carrier U) (F : Finset ι) :
    mixedFiniteUnionSet D F ⊆ carrier U := by
  rintro p ⟨i,_,hp⟩
  exact hD i hp

theorem mixedFiniteUnion_disjoint (D : ι → DefSet (M := M) Set.univ n a)
    (hD : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j))) (i : ι) (F : Finset ι) (hi : i ∉ F) :
    Disjoint (carrier (D i)) (mixedFiniteUnionSet D F) := by
  apply Set.disjoint_left.mpr
  rintro p hp ⟨j,hj,hpj⟩
  exact Set.disjoint_left.mp (hD i j (fun he => hi (he ▸ hj))) hp hpj

theorem mixedFiniteUnion_pullback (D : ι → DefSet (M := M) Set.univ n a)
    (hD : ∀ i, IsRVPullback (carrier (D i))) (F : Finset ι) : IsRVPullback (mixedFiniteUnionSet D F) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨i,hi,hp⟩ q hpq
  exact ⟨i,hi,(isRVPullback_iff _).mp (hD i) p hp q hpq⟩

end IntegrationInACVF.Section6
