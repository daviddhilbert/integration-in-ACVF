module

public import Integration7.NativePreparedMixedPartitions
public import Integration7.GeneratedBaseStandardContractions
public import IntegrationSection6.PreparedPartitionImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Simultaneous membership preparation and actual restricted special
bijections construct the whole finite pullback partition over C.base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ} {ι : Type} [Fintype ι]

theorem native_prepared_mixed_partition_exists (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (hAP : IsRVPullback (carrier A))
    (D : ι → DefSet (M := M) (C.base : Set M) (n+1) a)
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = nativeMixedFiniteUnionSet D Finset.univ) :
    Nonempty (NativePreparedMixedPartition A D) := by
  classical
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  obtain ⟨r,B,T,hT,hBP,hFlags⟩ := gamma_prepare_finite_membership_all_arity (P := G)
    C.saturated C.model00 C.small (generatedBaseVFField hGenerated) (Set.Subset.refl _) A hAP hA
    D Finset.univ (fun i _ => (gammaLogicInput G).real_set _ (setDefinable (D i)))
  choose R W hAlt hEnd hRK hW using fun i : ι =>
    special_restrict_boundary T (D i) (hDA i) none T.alternating
  let e : GammaIso G (carrier A) (carrier B) :=
    ⟨Equiv.ofBijective T.toMap T.bijective,(gammaLogicInput G).real_map_graph T.toMap⟩
  have hImage (i : ι) : carrier (R i) = gammaRestrictionTarget e (carrier (D i)) (hDA i) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx⟩ := (W i).bijective.surjective ⟨p,hp⟩
      refine ⟨x,?_⟩
      change (T.toMap ⟨x.val,hDA i x.property⟩).val = p
      exact (hW i x).symm.trans (congrArg (fun q : R i => q.val) hx)
    · rintro ⟨x,hx⟩
      have hv : ((W i).toMap x).val = p := (hW i x).trans hx
      exact Eq.mp (congrArg (fun z => z ∈ carrier (R i)) hv) ((W i).toMap x).property
  have hSubset (i : ι) : carrier (R i) ⊆ carrier B := by
    rw [hImage i]
    exact gammaRestrictionTarget_subset e (carrier (D i)) (hDA i)
  refine ⟨{
    arity := r
    target := B
    special := T
    pullback := hBP
    pieces := R
    pieceSpecial := W
    piecePullback := ?_
    subset := hSubset
    disjoint := ?_
    cover := ?_ }⟩
  · intro i
    rw [hImage i]
    exact prepared_partition_image_pullback T hBP (hDA i) (hFlags i (Finset.mem_univ i)) e (fun _ => rfl)
  · intro i j hij
    rw [hImage i,hImage j]
    apply Set.disjoint_left.mpr
    rintro p ⟨x,hx⟩ ⟨y,hy⟩
    have he := e.equiv.injective (Subtype.ext (hx.trans hy.symm))
    have hv := congrArg (fun q : carrier A => q.val) he
    exact Set.disjoint_left.mp (hDisj i j hij) x.property (hv.symm ▸ y.property)
  · ext p
    constructor
    · intro hp
      let x := T.inverseMap ⟨p,hp⟩
      obtain ⟨i,hi,hxi⟩ := (Set.ext_iff.mp hCover x.val).mp x.property
      refine ⟨i,hi,?_⟩
      rw [hImage i]
      refine ⟨⟨x.val,hxi⟩,?_⟩
      have he : (⟨x.val,hDA i hxi⟩ : A) = x := Subtype.ext rfl
      change (T.toMap ⟨x.val,hDA i hxi⟩).val = p
      rw [he]
      exact congrArg (fun q : B => q.val) (T.apply_inverse ⟨p,hp⟩)
    · rintro ⟨i,_,hp⟩
      exact hSubset i hp

end IntegrationInACVF.Section7
