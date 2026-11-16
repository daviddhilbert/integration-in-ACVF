module

public import Integration7.NativePreparedMixedPartitions
public import IntegrationSection6.PreparedPartitionImages
public import Section5.GammaRestriction

@[expose] public section

/-! Actual simultaneous pullback partitions retain original-Gamma
certificates on the global special bijection and every restricted chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a r : ℕ} {ι : Type} [Fintype ι]

theorem gamma_native_prepared_partition_of_membership
    (A : DefSet (M := M) S n a) (D : ι → DefSet (M := M) S n a)
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = nativeMixedFiniteUnionSet D Finset.univ)
    (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    {W : DefSet (M := M) S n r} (T : SpecialBijection A W)
    (hT : GammaChainDefinable B T.chain) (hWP : IsRVPullback (carrier W))
    (hFlags : ∀ i, Contractible (Map.comp (membershipMap A (D i)) T.inverseMap)) :
    ∃ Q : NativePreparedMixedPartition A D,
      GammaChainDefinable B Q.special.chain ∧ ∀ i, GammaChainDefinable B (Q.pieceSpecial i).chain := by
  choose R U hAlt hUG hSub hImage hU using fun i : ι =>
    SpecialBijection.restrict_gamma_at (gammaLogicInput B) T hT (D i) (hDA i) (hD i) none T.alternating
  let e : GammaIso B (carrier A) (carrier W) :=
    ⟨Equiv.ofBijective T.toMap T.bijective,GammaChainDefinable.graph (gammaLogicInput B) T.chain hT⟩
  have hImage' (i : ι) : carrier (R i) = gammaRestrictionTarget e (carrier (D i)) (hDA i) := hImage i
  have hSubset (i : ι) : carrier (R i) ⊆ carrier W := hSub i
  let Q : NativePreparedMixedPartition A D := {
    arity := r
    target := W
    special := T
    pullback := hWP
    pieces := R
    pieceSpecial := U
    piecePullback := by
      intro i
      rw [hImage' i]
      exact prepared_partition_image_pullback T hWP (hDA i) (hFlags i) e (fun _ => rfl)
    subset := hSubset
    disjoint := by
      intro i j hij
      rw [hImage' i,hImage' j]
      apply Set.disjoint_left.mpr
      rintro p ⟨x,hx⟩ ⟨y,hy⟩
      have he := e.equiv.injective (Subtype.ext (hx.trans hy.symm))
      have hv := congrArg (fun q : carrier A => q.val) he
      exact Set.disjoint_left.mp (hDisj i j hij) x.property (hv.symm ▸ y.property)
    cover := by
      ext p
      constructor
      · intro hp
        let x := T.inverseMap ⟨p,hp⟩
        obtain ⟨i,hi,hxi⟩ := (Set.ext_iff.mp hCover x.val).mp x.property
        refine ⟨i,hi,?_⟩
        rw [hImage' i]
        refine ⟨⟨x.val,hxi⟩,?_⟩
        have he : (⟨x.val,hDA i hxi⟩ : A) = x := Subtype.ext rfl
        change (T.toMap ⟨x.val,hDA i hxi⟩).val = p
        rw [he]
        exact congrArg (fun q : W => q.val) (T.apply_inverse ⟨p,hp⟩)
      · rintro ⟨i,_,hp⟩
        exact hSubset i hp }
  exact ⟨Q,hT,hUG⟩

end IntegrationInACVF.Section7
