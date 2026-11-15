import Integration7.NativeFiniteMixedUnions

/-! A finite partition of a subdomain extends to its ambient domain by
adjoining the actual definable complement as one additional piece. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {ι : Type} [Fintype ι]

def nativeMixedDifference (A L : DefSet (M := M) S n a) : DefSet (M := M) S n a :=
  PresentedSet.mk (carrier A \ carrier L)
    (@SpecialTransformations.DefinableGeometry.Space.Definable.sdiff LRV M (@CanonicalStructure.normalize M sM)
      (pointSpace n a) S (carrier A) (carrier L) (setDefinable A) (setDefinable L))

def nativeCompletedPartition (A L : DefSet (M := M) S n a)
    (D : ι → DefSet (M := M) S n a) : Option ι → DefSet (M := M) S n a
  | none => nativeMixedDifference A L
  | some i => D i

theorem native_completed_partition_subset (A L : DefSet (M := M) S n a)
    (D : ι → DefSet (M := M) S n a) (hLA : carrier L ⊆ carrier A)
    (hDL : ∀ i, carrier (D i) ⊆ carrier L) :
    ∀ i, carrier (nativeCompletedPartition A L D i) ⊆ carrier A := by
  intro i
  cases i with
  | none => exact Set.sdiff_subset
  | some i => exact (hDL i).trans hLA

theorem native_completed_partition_disjoint (A L : DefSet (M := M) S n a)
    (D : ι → DefSet (M := M) S n a) (hDL : ∀ i, carrier (D i) ⊆ carrier L)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j))) :
    ∀ i j, i ≠ j → Disjoint (carrier (nativeCompletedPartition A L D i))
      (carrier (nativeCompletedPartition A L D j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some j => exact Set.disjoint_left.mpr (fun p hp hq => hp.2 (hDL j hq))
  | some i =>
    cases j with
    | none => exact Set.disjoint_left.mpr (fun p hp hq => hq.2 (hDL i hp))
    | some j => exact hDisj i j (fun he => hij (congrArg some he))

theorem native_completed_partition_cover (A L : DefSet (M := M) S n a)
    (D : ι → DefSet (M := M) S n a) (hLA : carrier L ⊆ carrier A)
    (hDL : ∀ i, carrier (D i) ⊆ carrier L)
    (hCover : carrier L = nativeMixedFiniteUnionSet D Finset.univ) :
    carrier A = nativeMixedFiniteUnionSet (nativeCompletedPartition A L D) Finset.univ := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hL : p ∈ carrier L
    · obtain ⟨i,hi,hpi⟩ := (Set.ext_iff.mp hCover p).mp hL
      exact ⟨some i,Finset.mem_univ _,hpi⟩
    · exact ⟨none,Finset.mem_univ _,hp,hL⟩
  · rintro ⟨i,_,hp⟩
    exact native_completed_partition_subset A L D hLA hDL i hp

end IntegrationInACVF.Section7
