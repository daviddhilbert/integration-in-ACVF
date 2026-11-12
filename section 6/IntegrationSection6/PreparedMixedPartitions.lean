import IntegrationSection6.PreparedPartitionImages
import IntegrationSection6.GammaFiniteMixedUnions

/-! Simultaneously prepare every piece of a finite Gamma partition.
Each prepared piece is an actual RV-pullback, and is joined to its original
piece by an actual Gamma relatively unary chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ} {ι : Type} [Fintype ι]

structure PreparedMixedPartition (A : DefSet (M := M) Set.univ n a)
    (D : ι → DefSet (M := M) Set.univ n a) where
  arity : ℕ
  target : DefSet (M := M) Set.univ n arity
  special : SpecialBijection A target
  gamma : GammaChainDefinable B special.chain
  pullback : IsRVPullback (carrier target)
  pieces : ι → DefSet (M := M) Set.univ n arity
  definable : ∀ i, GammaSetDefinable B (carrier (pieces i))
  piecePullback : ∀ i, IsRVPullback (carrier (pieces i))
  subset : ∀ i, carrier (pieces i) ⊆ carrier target
  disjoint : ∀ i j, i ≠ j → Disjoint (carrier (pieces i)) (carrier (pieces j))
  cover : carrier target = mixedFiniteUnionSet pieces Finset.univ
  unary : ∀ i, GammaUnaryChain B n (carrier (D i)) (carrier (pieces i))

theorem prepared_mixed_partition_exists {κ : Cardinal} (hn : 0 < n) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
    (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (hAP : IsRVPullback (carrier A))
    (D : ι → DefSet (M := M) Set.univ n a) (hD : ∀ i, GammaSetDefinable B (carrier (D i)))
    (hDA : ∀ i, carrier (D i) ⊆ carrier A)
    (hDisj : ∀ i j, i ≠ j → Disjoint (carrier (D i)) (carrier (D j)))
    (hCover : carrier A = mixedFiniteUnionSet D Finset.univ) : Nonempty (PreparedMixedPartition (B := B) A D) := by
  obtain ⟨l,C,T,hT,hCP,hFlags⟩ := gamma_prepare_finite_membership_all_arity hs h00 hreal FBase
    (Set.subset_univ _) A hAP hA D Finset.univ (fun i _ => hD i)
  obtain ⟨t,ht⟩ := gamma_special_unary_chain_exists hn T.chain hT
  let Y (i : ι) := gammaRestrictionTarget t.toIso (carrier (D i)) (hDA i)
  have hY (i : ι) : GammaSetDefinable B (Y i) :=
    (gammaRestrictionIso t.toIso (carrier (D i)) (hDA i) (hD i)).target_definable (gammaLogicInput B)
  let E (i : ι) := gammaDefSetUniv (Y i) (hY i)
  have hEC (i : ι) : carrier (E i) ⊆ carrier C := gammaRestrictionTarget_subset t.toIso _ (hDA i)
  choose u hu using fun i : ι => t.restrict_exact (carrier (D i)) (hDA i) (hD i)
  refine ⟨{
    arity := l
    target := C
    special := T
    gamma := hT
    pullback := hCP
    pieces := E
    definable := hY
    piecePullback := ?_
    subset := hEC
    disjoint := ?_
    cover := ?_
    unary := u }⟩
  · intro i
    exact prepared_partition_image_pullback T hCP (hDA i) (hFlags i (Finset.mem_univ i)) t.toIso ht
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro p ⟨x,hx⟩ ⟨y,hy⟩
    have he := t.toIso.equiv.injective (Subtype.ext (hx.trans hy.symm))
    have hval := congrArg (fun z : carrier A => z.val) he
    exact Set.disjoint_left.mp (hDisj i j hij) x.property (hval.symm ▸ y.property)
  · ext p
    constructor
    · intro hp
      let c : C := ⟨p,hp⟩
      let x := t.toIso.equiv.symm c
      obtain ⟨i,hi,hxi⟩ := (Set.ext_iff.mp hCover x.val).mp x.property
      refine ⟨i,hi,⟨⟨x.val,hxi⟩,?_⟩⟩
      change (t.toIso.equiv ⟨x.val,hDA i hxi⟩).val = p
      have he : (⟨x.val,hDA i hxi⟩ : carrier A) = x := Subtype.ext rfl
      rw [he]
      exact congrArg (fun z : carrier C => z.val) (t.toIso.equiv.apply_symm_apply c)
    · rintro ⟨i,_,hp⟩
      exact hEC i hp

end IntegrationInACVF.Section6
