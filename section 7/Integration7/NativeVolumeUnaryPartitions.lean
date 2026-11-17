module

public import Integration7.UnaryPartitionVolumeDensities
public import Integration7.NativeFiniteMixedUnions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Section 5.6 as a finite partition by actual real-definable domains
and actual unary chains carrying the restricted original volume forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

structure NativeVolumeUnaryPartition (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (B : DefSet (M := M) (C.base : Set M) (n+1) b)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B)) where
  index : Type
  finite : Fintype index
  source : index → DefSet (M := M) (C.base : Set M) (n+1) a
  target : index → DefSet (M := M) (C.base : Set M) (n+1) b
  sourceSubset : ∀ i, carrier (source i) ⊆ carrier A
  targetSubset : ∀ i, carrier (target i) ⊆ carrier B
  sourceDisjoint : ∀ i j, i ≠ j → Disjoint (carrier (source i)) (carrier (source j))
  targetDisjoint : ∀ i j, i ≠ j → Disjoint (carrier (target i)) (carrier (target j))
  sourceCover : carrier A = nativeMixedFiniteUnionSet source (@Finset.univ index finite)
  targetCover : carrier B = nativeMixedFiniteUnionSet target (@Finset.univ index finite)
  chain : ∀ i, UnaryChain (C.base : Set M) (n+1) (source i) (target i)
  volume : ∀ i, unaryChainVolumeData hc (chain i)
    (ω.restrict (show (rawSpecialSet hc (source i)).carrier ⊆ (rawSpecialSet hc A).carrier from sourceSubset i))
    (π.restrict (show (rawSpecialSet hc (target i)).carrier ⊆ (rawSpecialSet hc B).carrier from targetSubset i))

theorem native_volume_unary_partition_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (f : Map A B) (hf : Function.Bijective f)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f)) :
    Nonempty (NativeVolumeUnaryPartition hc C A B ω π) := by
  classical
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hfΓ : GammaGraphDefinable G (pointMapGraph f) := (gammaLogicInput G).real_map_graph f
  let e : GammaIso G (carrier A) (carrier B) := ⟨Equiv.ofBijective f hf,hfΓ⟩
  obtain ⟨Q,_⟩ := lemma_5_6_iso (G := G) C.uncountable.le C.saturated C.model00 C.small γ hγ1 e
  choose E hDr hEr hEB t ht hVal hData using fun i : Q.pieces =>
    unary_partition_volume_densities (G := G) hc C (Nat.zero_lt_succ n) hNames f hf hfΓ ω π hm Q i.val i.property
  let D (i : Q.pieces) : DefSet (M := M) (C.base : Set M) (n+1) a := PresentedSet.mk i.val (hDr i)
  let R (i : Q.pieces) : DefSet (M := M) (C.base : Set M) (n+1) b := PresentedSet.mk (E i) (hEr i)
  have hImage (i : Q.pieces) : E i = gammaRestrictionTarget e i.val (Q.subset i.val i.property) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx⟩ := (t i).bijective.surjective ⟨p,hp⟩
      refine ⟨x,?_⟩
      exact (hVal i x).symm.trans (congrArg (fun q : R i => q.val) hx)
    · rintro ⟨x,hx⟩
      have hv : ((t i).toMap x).val = p := (hVal i x).trans hx
      exact Eq.mp (congrArg (fun z => z ∈ E i) hv) ((t i).toMap x).property
  refine ⟨{
    index := Q.pieces
    finite := inferInstance
    source := D
    target := R
    sourceSubset := fun i => Q.subset i.val i.property
    targetSubset := hEB
    sourceDisjoint := ?_
    targetDisjoint := ?_
    sourceCover := ?_
    targetCover := ?_
    chain := t
    volume := hData }⟩
  · intro i j hij
    exact Q.disjoint i.val i.property j.val j.property (fun he => hij (Subtype.ext he))
  · intro i j hij
    change Disjoint (E i) (E j)
    rw [hImage i,hImage j]
    apply Set.disjoint_left.mpr
    rintro p ⟨x,hx⟩ ⟨y,hy⟩
    have he := e.equiv.injective (Subtype.ext (hx.trans hy.symm))
    have hv := congrArg (fun q : carrier A => q.val) he
    exact Set.disjoint_left.mp (Q.disjoint i.val i.property j.val j.property
      (fun he => hij (Subtype.ext he))) x.property (hv.symm ▸ y.property)
  · ext p
    constructor
    · intro hp
      obtain ⟨i,hi,hpi⟩ := Q.cover ⟨p,hp⟩
      exact ⟨⟨i,hi⟩,Finset.mem_univ _,hpi⟩
    · rintro ⟨i,_,hp⟩
      exact Q.subset i.val i.property hp
  · ext p
    constructor
    · intro hp
      let x := e.equiv.symm ⟨p,hp⟩
      obtain ⟨i,hi,hxi⟩ := Q.cover x
      refine ⟨⟨i,hi⟩,Finset.mem_univ _,?_⟩
      change p ∈ E ⟨i,hi⟩
      rw [hImage ⟨i,hi⟩]
      refine ⟨⟨x.val,hxi⟩,?_⟩
      have he : (⟨x.val,Q.subset i hi hxi⟩ : carrier A) = x := Subtype.ext rfl
      change (e.equiv ⟨x.val,Q.subset i hi hxi⟩).val = p
      rw [he]
      exact congrArg (fun q : carrier B => q.val) (e.equiv.apply_symm_apply ⟨p,hp⟩)
    · rintro ⟨i,_,hp⟩
      exact hEB i hp

end IntegrationInACVF.Section7
