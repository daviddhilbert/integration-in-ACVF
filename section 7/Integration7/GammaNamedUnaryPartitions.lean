import Integration7.GammaNamedPreparedChains
import Integration7.NativeVolumeUnaryPartitions

/-! Gamma-named Section 5.6 partitions: an actual mixed volume bijection with
a Gamma graph over `G` has a finite partition into actual pieces carrying
Gamma unary chains, and the partition pieces are Gamma-definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem gamma_unary_chain_graph {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (t : UnaryChain S n A B) (ht : GammaUnaryChainDefinable G t) :
    GammaGraphDefinable G (pointMapGraph t.toMap) := by
  induction t with
  | nil A =>
    apply GammaGraphDefinable.congr (gamma_vf_identity_graph (B := G) _ ht)
    intro p q
    constructor
    · rintro ⟨hp,rfl⟩
      exact ⟨⟨p,hp⟩,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨u.property,rfl⟩
  | cons i f hf hi tail ih =>
    apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph ht.1 (ih ht.2))
    intro p q
    constructor
    · rintro ⟨z,⟨u,rfl,rfl⟩,⟨v,hv,rfl⟩⟩
      have hv' : v = f u := Subtype.ext hv
      subst hv'
      exact ⟨u,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨(f u).val,⟨u,rfl,rfl⟩,⟨f u,rfl,rfl⟩⟩

theorem gamma_unary_chain_target {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (t : UnaryChain S n A B) (ht : GammaUnaryChainDefinable G t) : GammaSetDefinable G (carrier B) := by
  have h := (gammaLogicInput G).image_graph (gamma_unary_chain_graph t ht)
  convert h using 1
  ext q
  constructor
  · intro hq
    obtain ⟨u,hu⟩ := t.bijective.2 ⟨q,hq⟩
    exact ⟨u.val,u,rfl,congrArg Subtype.val hu⟩
  · rintro ⟨p,u,rfl,rfl⟩
    exact (t.toMap u).property

namespace GammaNamed

theorem native_volume_unary_partition_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (f : Map A B) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable G (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f)) :
    ∃ Q : NativeVolumeUnaryPartition hc C A B ω π,
      (∀ i, GammaSetDefinable G (carrier (Q.source i))) ∧
      (∀ i, GammaSetDefinable G (carrier (Q.target i))) ∧
      ∀ i, GammaUnaryChainDefinable G (Q.chain i) := by
  classical
  let e : GammaIso G (carrier A) (carrier B) := ⟨Equiv.ofBijective f hf,hfΓ⟩
  obtain ⟨Q,_⟩ := lemma_5_6_iso (G := G) C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) γ hγ1 e
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
    volume := hData },
    fun i => gamma_unary_chain_source (t i) (ht i),
    fun i => gamma_unary_chain_target (t i) (ht i),ht⟩
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

end GammaNamed
end IntegrationInACVF.Section7
