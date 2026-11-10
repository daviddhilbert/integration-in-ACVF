module

public import IntegrationSection3.NamedFamilyFibres
public import IntegrationSection3.FibreSupportFormulas
public import IntegrationSection3.RelationalPreimages
public import IntegrationSection3.AtomicFiniteFibres
public import IntegrationSection3.CoarseRelationFibres
public import IntegrationSection3.SupportInsideBall

@[expose] public section

/-! Source-side support alternative for 3.11. The finite relation bound
is proved from source atomicity. No saturation or definable choice is used. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ProperInverseSupports

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

theorem proper_inverse_supports (hp : B.real.Definable L p.codes)
    (hq : q.IsDefinable L B.real) {U C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hinj : Function.Injective U)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    {balls : Set (Set M)} (hl : IsLaminar balls) (htop : (Set.univ : Set M) ∈ balls)
    (hnf : MinimalBallSupport.AvoidsFiniteProperSubballs balls) (hUb : ∀ j, U j ∈ balls)
    (i : J) (hiDef : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ U i})
    (hiAtomic : ImaginaryBaseFamilies.CompleteType (L := L) p B (U i))
    (hfinite : ∀ x ∈ U i, {y | (x,y) ∈ R}.Finite)
    {A : Set M} (hAtomic : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T) (hTinfinite : T.Infinite)
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (F : J → Finset (Set M))
    (hF : ∀ j ∈ T, MinimalBallSupport.IsMinimalSupport balls (F j)
      (RelationalPreimages.family R C j))
    (hcover : ∀ j ∈ T, ∀ b ∈ F j, ∃ k, U k = b)
    (hsource : ∀ j ∈ T, RelationalPreimages.family R C j ⊆ U i) :
    ∀ j ∈ T, ∀ b ∈ F j, b ⊂ U i := by
  classical
  let D := RelationalPreimages.family R C
  have hD : ImaginaryBaseFamilies.Relation (L := L) p B q D :=
    RelationalPreimages.family_definable hp hR hC
  obtain ⟨j0,hj0⟩ := hTinfinite.nonempty
  let n := (F j0).card
  have hcard (j : J) (hj : j ∈ T) : (F j).card = n := by
    have he (m : ℕ) : FibreSupportFormulas.HasSupport U D m j ↔
        FibreSupportFormulas.HasSupport U D m j0 := by
      rcases AtomicRegions.uniform_property hp hAtomic hT
        (FibreSupportFormulas.hasSupport_family hp hq.1 hU hD m) hC hne hsub hdis with hall | hnone
      · exact iff_of_true (hall hj) (hall hj0)
      · exact iff_of_false (fun h => Set.disjoint_left.mp hnone hj h)
          (fun h => Set.disjoint_left.mp hnone hj0 h)
    have hjS := FibreSupportFormulas.hasSupport_of_support (hF j hj).1.2 (hcover j hj)
    have h0S := FibreSupportFormulas.hasSupport_of_support (hF j0 hj0).1.2 (hcover j0 hj0)
    exact le_antisymm
      (FibreSupportFormulas.card_le_of_hasSupport hUb (hF j hj) ((he n).mpr h0S))
      (FibreSupportFormulas.card_le_of_hasSupport hUb (hF j0 hj0) ((he (F j).card).mp hjS))
  let P := {j | FibreSupportFormulas.SupportMember U D n j i}
  have hP : ImaginaryBaseFamilies.Family (L := L) p B q P :=
    NamedFamilyFibres.binary_fibre hp hq.1
      (FibreSupportFormulas.supportMember_definable hp hq hU hD n) i
      (NamedFamilyFibres.singleton_of_definable hp hq.1 hU hinj i hiDef)
  have hPiff (j : J) (hj : j ∈ T) : j ∈ P ↔ U i ∈ F j := by
    have he := FibreSupportFormulas.supportMember_iff_canonical hinj hl htop hnf hUb
      (hF j hj) (hcover j hj) i
    rwa [hcard j hj] at he
  have hNone : ∀ j ∈ T, U i ∉ F j := by
    rcases AtomicRegions.uniform_property hp hAtomic hT hP hC hne hsub hdis with hall | hnone
    · obtain ⟨N,hN⟩ := AtomicFiniteFibres.uniform_bound hp hiAtomic hR hfinite
      have hcoarse (j : J) (hj : j ∈ T) : CoarsePartition.SmallIn balls (U i)
          (U i \ {x | ∃ y ∈ C j, (x,y) ∈ R}) := by
        have hc := SupportInsideBall.parent_mem_small_complement hl (hsource j hj)
          (hF j hj) ((hPiff j hj).mp (hall hj))
        convert hc using 1
        ext x
        exact and_congr_right fun _ => not_congr (exists_congr fun y => and_comm)
      exact (hTinfinite (CoarseRelationFibres.coarse_indices_finite hnf (hUb i)
        (fun x y => (x,y) ∈ R) C hdis N hfinite hN hcoarse)).elim
    · exact fun j hj hjF => Set.disjoint_left.mp hnone hj ((hPiff j hj).mpr hjF)
  intro j hj b hb
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨SupportInsideBall.support_subset_parent hl htop hnf (hUb i) (hsource j hj) (hF j hj) b hb,?_⟩
  intro he
  exact hNone j hj (he ▸ hb)

end IntegrationInACVF.Section3.ProperInverseSupports
