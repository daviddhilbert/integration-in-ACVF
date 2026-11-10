module

public import IntegrationSection3.MinimalBallSupport

@[expose] public section

/-! Finite/cofinite traces on a partition whose proper test balls live
in single classes. The actual maximal-open-subball geometry is separate. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport

namespace IntegrationInACVF.Section3.FiniteCofiniteClasses

variable {X J : Type*}

theorem outside_finite_same_profile {P : Set X} {T : Set J} (C : J → Set X)
    (hsub : ∀ j ∈ T, C j ⊆ P) (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (F : Finset (Set X))
    (hF : ∀ b ∈ F, P ⊆ b ∨ Disjoint P b ∨ ∃ j ∈ T, b ∩ P ⊆ C j) :
    ∃ E : Set J, E.Finite ∧ ∀ j ∈ T, j ∉ E → ∀ k ∈ T, k ∉ E →
      ∀ x ∈ C j, ∀ y ∈ C k, ∀ b ∈ F, x ∈ b ↔ y ∈ b := by
  classical
  let E (b : Set X) := {j | j ∈ T ∧ (b ∩ P).Nonempty ∧ b ∩ P ⊆ C j}
  have he (b : Set X) : (E b).Subsingleton := by
    intro j hj k hk
    by_contra hne
    obtain ⟨x,hx⟩ := hj.2.1
    exact Set.disjoint_left.mp (hdis hj.1 hk.1 hne) (hj.2.2 hx) (hk.2.2 hx)
  have hf := F.finite_toSet.biUnion (fun b _ => (he b).finite)
  refine ⟨_,hf,?_⟩
  intro j hj hjE k hk hkE x hx y hy b hb
  have hnot (i : J) (hi : i ∈ T) (hiE : i ∉ ⋃ b ∈ (F : Set (Set X)), E b)
      (z : X) (hz : z ∈ C i) (hsmall : ∃ l ∈ T, b ∩ P ⊆ C l) : z ∉ b := by
    intro hzb
    obtain ⟨l,hl,hbl⟩ := hsmall
    have hzi : z ∈ b ∩ P := ⟨hzb,hsub i hi hz⟩
    have hlE : l ∈ ⋃ b ∈ (F : Set (Set X)), E b :=
      Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hb,hl,⟨z,hzi⟩,hbl⟩⟩
    by_cases hil : i = l
    · exact hiE (hil.symm ▸ hlE)
    · exact Set.disjoint_left.mp (hdis hi hl hil) hz (hbl hzi)
  rcases hF b hb with hPb | hdisPb | hsmall
  · exact iff_of_true (hPb (hsub j hj hx)) (hPb (hsub k hk hy))
  · exact iff_of_false (fun h => Set.disjoint_left.mp hdisPb (hsub j hj hx) h)
      (fun h => Set.disjoint_left.mp hdisPb (hsub k hk hy) h)
  · exact iff_of_false (hnot j hj hjE x hx hsmall) (hnot k hk hkE y hy hsmall)

theorem finite_or_cofinite {P A : Set X} {T S : Set J} (C : J → Set X)
    (hST : S ⊆ T) (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ P)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (F : Finset (Set X)) (hA : Supports F A)
    (hF : ∀ b ∈ F, P ⊆ b ∨ Disjoint P b ∨ ∃ j ∈ T, b ∩ P ⊆ C j)
    (htrace : ∀ j ∈ T, ∀ x ∈ C j, x ∈ A ↔ j ∈ S) : S.Finite ∨ (T \ S).Finite := by
  classical
  obtain ⟨E,hE,hprofiles⟩ := outside_finite_same_profile C hsub hdis F hF
  by_cases hw : ∃ j ∈ S, j ∉ E
  · obtain ⟨j,hj,hjE⟩ := hw
    obtain ⟨x,hx⟩ := hne j (hST hj)
    have hxA := (htrace j (hST hj) x hx).mpr hj
    right
    apply hE.subset
    rintro k ⟨hk,hkS⟩
    by_contra hkE
    obtain ⟨y,hy⟩ := hne k hk
    have hyA := (hA x y (hprofiles j (hST hj) hjE k hk hkE x hx y hy)).mp hxA
    exact hkS ((htrace k hk y hy).mp hyA)
  · left
    exact hE.subset (fun j hj => by by_contra hjE; exact hw ⟨j,hj,hjE⟩)

end IntegrationInACVF.Section3.FiniteCofiniteClasses
