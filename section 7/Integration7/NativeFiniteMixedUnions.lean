module

public import IntegrationSection5.HeadContractionGeometry

@[expose] public section

/-! Finite mixed unions over the actual real parameter base, without
replacing that base by the whole model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {ι : Type}

def nativeMixedFiniteUnionSet (D : ι → DefSet (M := M) S n a) (F : Finset ι) : Set (Point (M := M) n a) :=
  {p | ∃ i ∈ F, p ∈ carrier (D i)}

theorem native_mixed_union_empty (D : ι → DefSet (M := M) S n a) : nativeMixedFiniteUnionSet D ∅ = ∅ := by
  ext p
  simp [nativeMixedFiniteUnionSet]

theorem native_mixed_union_insert [DecidableEq ι] (D : ι → DefSet (M := M) S n a) (i : ι) (F : Finset ι) :
    nativeMixedFiniteUnionSet D (insert i F) = carrier (D i) ∪ nativeMixedFiniteUnionSet D F := by
  classical
  ext p
  constructor
  · rintro ⟨j,hj,hp⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hp
    · exact Or.inr ⟨j,hj,hp⟩
  · rintro (hp | ⟨j,hj,hp⟩)
    · exact ⟨i,Finset.mem_insert_self _ _,hp⟩
    · exact ⟨j,Finset.mem_insert_of_mem hj,hp⟩

theorem native_mixed_union_definable (D : ι → DefSet (M := M) S n a) (F : Finset ι) :
    SetDefinable (pointSpace (M := M) n a) S (nativeMixedFiniteUnionSet D F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    rw [native_mixed_union_empty (M := M) D]
    exact setDefinable (@SpecialTransformations.DefinableGeometry.DefSet.empty LRV M
      (@CanonicalStructure.normalize M sM) (pointSpace n a) S)
  | insert i F hi ih =>
    rw [native_mixed_union_insert (M := M) D i F]
    exact @SpecialTransformations.DefinableGeometry.Space.Definable.union LRV M
      (@CanonicalStructure.normalize M sM) (pointSpace n a) S (carrier (D i))
      (nativeMixedFiniteUnionSet D F) (setDefinable (D i)) ih

def nativeMixedFiniteUnion (D : ι → DefSet (M := M) S n a) (F : Finset ι) : DefSet (M := M) S n a :=
  PresentedSet.mk (nativeMixedFiniteUnionSet D F) (native_mixed_union_definable D F)

theorem native_mixed_union_subset {U : DefSet (M := M) S n a}
    (D : ι → DefSet (M := M) S n a) (hD : ∀ i, carrier (D i) ⊆ carrier U) (F : Finset ι) :
    nativeMixedFiniteUnionSet D F ⊆ carrier U := by
  rintro p ⟨i,hi,hp⟩
  exact hD i hp

theorem native_mixed_union_disjoint (D : ι → DefSet (M := M) S n a)
    (hD : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j))) (i : ι) (F : Finset ι) (hi : i ∉ F) :
    Disjoint (carrier (D i)) (nativeMixedFiniteUnionSet D F) := by
  apply Set.disjoint_left.mpr
  rintro p hp ⟨j,hj,hpj⟩
  exact Set.disjoint_left.mp (hD i j (fun he => hi (he ▸ hj))) hp hpj

theorem native_mixed_union_pullback (D : ι → DefSet (M := M) S n a)
    (hD : ∀ i, IsRVPullback (carrier (D i))) (F : Finset ι) :
    IsRVPullback (nativeMixedFiniteUnionSet D F) := by
  apply (isRVPullback_iff _).mpr
  rintro p ⟨i,hi,hp⟩ q hpq
  exact ⟨i,hi,(isRVPullback_iff _).mp (hD i) p hp q hpq⟩

end IntegrationInACVF.Section7
