module

public import IntegrationSection3.BoundedCoverFormulas

@[expose] public section

/-! An atomic punctured ball has no nontrivial finite definable disjoint
partition by nonempty finite-ball-support sets. Only the entire index and
membership families are required to be definable. The parent name must
be definable over the same original base; no centre or hole is named. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.MinimalBallSupport

namespace IntegrationInACVF.Section3.AtomicPuncturedPartition

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

theorem subsingleton (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes)
    {balls : Set (Set M)} (hl : IsLaminar balls) (hnf : AvoidsFiniteProperSubballs balls)
    {U : J → Set M} (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hUballs : ∀ j, U j ∈ balls) (hballs : ∀ b ∈ balls, ∃ j, U j = b)
    (i : J) (hi : ImaginaryBaseFamilies.Family (L := L) p B q {i})
    {A : Set M} (hAtomic : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    (H : Finset (Set M)) (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ U i)
    (hA : A = U i \ {x | ∃ h ∈ H, x ∈ h})
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    (hTfin : T.Finite) {C : J → Set M}
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    (hsupport : ∀ j ∈ T, HasFiniteBallSupport balls (C j))
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hcover : A ⊆ {x | ∃ j ∈ T, x ∈ C j})
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k)) : T.Subsingleton := by
  obtain ⟨F,hF,hFS⟩ := CoarsePartition.common_support hTfin hsupport
  have hAP : A ⊆ U i := by
    rw [hA]
    exact Set.sdiff_subset
  have hCP : ∀ j ∈ T, C j ⊆ U i := fun j hj => (hsub j hj).trans hAP
  have hcov : U i \ {x | ∃ h ∈ H, x ∈ h} ⊆ {x | ∃ j ∈ T, x ∈ C j} := by
    rwa [← hA]
  obtain ⟨N,j,⟨hj,hjbig⟩,hunique⟩ := CoarsePartition.unique_outer_piece_at_bound
    hl hnf (hUballs i) hH hF hFS hCP hcov hdis
  let Q := {k | k ∈ T ∧ ∃ l ∈ ({i} : Set J), ¬ BoundedCoverFormulas.AtMostCover U C N ![l,k]}
  have hQ := BoundedCoverFormulas.uncoveredFamily_definable hp hq hU hC hi hT N
  have he : Q = {j} := by
    ext k
    constructor
    · rintro ⟨hk,l,hl,hn⟩
      have hli : l = i := hl
      rw [hli] at hn
      exact hunique k ⟨hk,fun hc => hn
        ((BoundedCoverFormulas.atMostCover_iff hUballs hballs i k N).mpr hc)⟩
    · intro hk
      have hkj : k = j := hk
      subst k
      exact ⟨hj,i,rfl,fun hc => hjbig
        ((BoundedCoverFormulas.atMostCover_iff hUballs hballs i j N).mp hc)⟩
  have hSingle : ImaginaryBaseFamilies.Family (L := L) p B q {j} := by
    change ImaginaryBaseFamilies.Family (L := L) p B q Q at hQ
    rwa [he] at hQ
  have hd : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ C j} := by
    have hr := ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp hSingle hC)
    convert hr using 1
    ext z
    change (z 0 ∈ C j) ↔ ∃ k, k = j ∧ z 0 ∈ C k
    constructor
    · intro hx
      exact ⟨j,rfl,hx⟩
    · rintro ⟨k,hkj,hx⟩
      rwa [hkj] at hx
  have hall : A ⊆ C j := by
    rcases hAtomic (C j) hd with h | h
    · exact h
    · obtain ⟨x,hx⟩ := hne j hj
      exact (Set.disjoint_left.mp h (hsub j hj hx) hx).elim
  have heach : ∀ k ∈ T, k = j := by
    intro k hk
    by_contra hkj
    obtain ⟨x,hx⟩ := hne k hk
    exact Set.disjoint_left.mp (hdis hk hj hkj) hx (hall (hsub k hk hx))
  intro k hk l hl
  exact (heach k hk).trans (heach l hl).symm

end IntegrationInACVF.Section3.AtomicPuncturedPartition
