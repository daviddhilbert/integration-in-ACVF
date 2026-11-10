module

public import IntegrationSection3.ImaginaryTupleFormulas
public import IntegrationSection3.AtomicRegions

@[expose] public section

/-! Uniform finite-support tests for interpreted families. A support tuple
is quantified through all its codes, so the test adds no representatives. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.ImaginaryTupleFormulas

namespace IntegrationInACVF.Section3.FibreSupportFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def SupportsTuple (U R : J → Set M) (n : ℕ) (a : Fin (n+1) → J) : Prop :=
  ∀ x y : M, (∀ i : Fin n, x ∈ U (a i.succ) ↔ y ∈ U (a i.succ)) →
    (x ∈ R (a 0) ↔ y ∈ R (a 0))

theorem supportsTuple_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U R : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hR : ImaginaryBaseFamilies.Relation (L := L) p B q R) (n : ℕ) :
    Predicate (L := L) p B q (SupportsTuple U R n) := by
  let π (i : Fin (n+1)) (j : Fin 2) : η ⊕ Fin 1 → ((Fin (n+1) × η) ⊕ Fin 2) :=
    Sum.elim (fun e => .inl (i,e)) (fun _ => .inr j)
  have hprofile := OverBase.forall_finite (fun i : Fin n =>
    SupportFormulas.iff_definable hp (hU.preimage_comp (π i.succ 0))
      (hU.preimage_comp (π i.succ 1))) hp
  have hrow := SupportFormulas.iff_definable hp (hR.preimage_comp (π 0 0)) (hR.preimage_comp (π 0 1))
  have hd := OverBase.forall_block (SupportFormulas.imp_definable hp hprofile hrow) hp
  have hc := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin (n+1)))
  unfold Predicate
  convert OverBase.inter hc hd hp using 1
  ext c
  have he (t : Fin 2 → M) (i : Fin (n+1)) (j : Fin 2) :
      Sum.elim c t ∘ π i j = Sum.elim (fun e => c (i,e)) ![t j] := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => fin_cases e; rfl
  change (∃ hc : c ∈ tupleCodes q (Fin (n+1)),
      SupportsTuple U R n ((tuplePresentation q (Fin (n+1))).decode ⟨c,hc⟩)) ↔
    (c ∈ tupleCodes q (Fin (n+1)) ∧ ∀ t : Fin 2 → M,
      (∀ i : Fin n, Sum.elim c t ∘ π i.succ 0 ∈ q.relationPullback U ↔
        Sum.elim c t ∘ π i.succ 1 ∈ q.relationPullback U) →
      (Sum.elim c t ∘ π 0 0 ∈ q.relationPullback R ↔
        Sum.elim c t ∘ π 0 1 ∈ q.relationPullback R))
  simp only [he]
  constructor
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun t ht => ?_⟩
    have hm (V : J → Set M) (i : Fin (n+1)) (j : Fin 2) :=
      q.mem_relationPullback V ⟨(fun e => c (i,e)),hc i⟩ (t j)
    exact (hm R 0 0).trans ((h (t 0) (t 1) (fun i =>
      (hm U i.succ 0).symm.trans ((ht i).trans (hm U i.succ 1)))).trans (hm R 0 1).symm)
  · rintro ⟨hc,h⟩
    refine ⟨hc,fun x y hxy => ?_⟩
    have hm (V : J → Set M) (i : Fin (n+1)) (z : M) :=
      q.mem_relationPullback V ⟨(fun e => c (i,e)),hc i⟩ z
    exact (hm R 0 x).symm.trans ((h ![x,y] (fun i =>
      (hm U i.succ x).trans ((hxy i).trans (hm U i.succ y).symm))).trans (hm R 0 y))

theorem supportsTuple_iff (U R : J → Set M) (n : ℕ) (a : Fin (n+1) → J) :
    SupportsTuple U R n a ↔ MinimalBallSupport.Supports
      (Finset.univ.image (fun i : Fin n => U (a i.succ))) (R (a 0)) := by
  classical
  constructor
  · intro h x y hxy
    exact h x y (fun i => hxy _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  · intro h x y hxy
    apply h x y
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact hxy i

def HasSupport (U R : J → Set M) (n : ℕ) (j : J) : Prop :=
  ∃ b : Fin n → J, SupportsTuple U R n (Fin.cases j b)

theorem hasSupport_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U R : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hR : ImaginaryBaseFamilies.Relation (L := L) p B q R) (n : ℕ) :
    Predicate (L := L) p B q (fun a : Fin 1 → J => HasSupport U R n (a 0)) := by
  have hs := ImaginaryTupleFormulas.reindex hp hq (supportsTuple_definable hp hq hU hR n)
    (Fin.cases (.inl 0) (fun i => .inr i) : Fin (n+1) → Fin 1 ⊕ Fin n)
  have hd := ImaginaryTupleFormulas.exists_block hs
  unfold Predicate at hd ⊢
  convert hd using 1
  congr 1

theorem hasSupport_family (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U R : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hR : ImaginaryBaseFamilies.Relation (L := L) p B q R) (n : ℕ) :
    ImaginaryBaseFamilies.Family (L := L) p B q {j | HasSupport U R n j} := by
  have hd := hasSupport_definable hp hq hU hR n
  unfold Predicate at hd
  have he := hd.preimage_comp (fun p : Fin 1 × η => p.2)
  change OverBase (L := L) p B (q.pullback {j | HasSupport U R n j})
  convert he using 1
  ext c
  constructor
  · rintro ⟨hc,h⟩
    exact ⟨(fun _ => hc),h⟩
  · rintro ⟨hc,h⟩
    exact ⟨hc 0,h⟩

theorem hasSupport_of_support {U R : J → Set M} {j : J} {F : Finset (Set M)}
    (hF : MinimalBallSupport.Supports F (R j)) (hcover : ∀ b ∈ F, ∃ k, U k = b) :
    HasSupport U R F.card j := by
  classical
  let e : Fin F.card ≃ F := F.equivFin.symm
  choose t ht using fun i : Fin F.card => hcover (e i).val (e i).property
  refine ⟨t,(supportsTuple_iff U R F.card (Fin.cases j t)).mpr ?_⟩
  have he : Finset.univ.image (fun i : Fin F.card => U (t i)) = F := by
    ext b
    constructor
    · rintro hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      exact (ht i).symm ▸ (e i).property
    · intro hb
      let i := e.symm ⟨b,hb⟩
      have hi : (e i).val = b := congrArg Subtype.val (e.apply_symm_apply ⟨b,hb⟩)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,(ht i).trans hi⟩
  change MinimalBallSupport.Supports (Finset.univ.image (fun i => U (t i))) (R j)
  rwa [he]

theorem card_le_of_hasSupport {balls : Set (Set M)} {U R : J → Set M}
    (hU : ∀ j, U j ∈ balls) {j : J} {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport balls F (R j)) {n : ℕ}
    (hs : HasSupport U R n j) : F.card ≤ n := by
  classical
  obtain ⟨t,ht⟩ := hs
  let G := Finset.univ.image (fun i : Fin n => U (t i))
  have hG : MinimalBallSupport.IsSupport balls G (R j) := by
    constructor
    · intro b hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      exact hU (t i)
    · have hs := (supportsTuple_iff U R n (Fin.cases j t)).mp ht
      simpa only [Fin.cases_zero,Fin.cases_succ] using hs
  exact (hF.2 G hG).trans (by simpa only [Finset.card_univ,Fintype.card_fin] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => U (t i))))

/-- Minimal support size is constant on a definable disjoint family
inside a complete type. The index family may be infinite. -/
theorem uniform_minimal_card (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U R C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hR : ImaginaryBaseFamilies.Relation (L := L) p B q R)
    {balls : Set (Set M)} (hUb : ∀ j, U j ∈ balls)
    (hcover : ∀ b ∈ balls, ∃ j, U j = b)
    {A : Set M} (hA : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    {j k : J} (hj : j ∈ T) (hk : k ∈ T) {F G : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport balls F (R j))
    (hG : MinimalBallSupport.IsMinimalSupport balls G (R k)) : F.card = G.card := by
  have he (n : ℕ) : HasSupport U R n j ↔ HasSupport U R n k := by
    rcases AtomicRegions.uniform_property hp hA hT (hasSupport_family hp hq hU hR n)
      hC hne hsub hdis with hall | hnone
    · exact iff_of_true (hall hj) (hall hk)
    · exact iff_of_false (fun h => Set.disjoint_left.mp hnone hj h)
        (fun h => Set.disjoint_left.mp hnone hk h)
  have hf := hasSupport_of_support hF.1.2 (fun b hb => hcover b (hF.1.1 b hb))
  have hg := hasSupport_of_support hG.1.2 (fun b hb => hcover b (hG.1.1 b hb))
  exact le_antisymm (card_le_of_hasSupport hUb hF ((he G.card).mpr hg))
    (card_le_of_hasSupport hUb hG ((he F.card).mp hf))

def SupportMember (U R : J → Set M) (n : ℕ) (j k : J) : Prop :=
  ∃ b : Fin n → J, SupportsTuple U R n (Fin.cases j b) ∧ k ∈ Set.range b

/-- A single formula defines support membership jointly with the fibre
index. Fixing an arbitrary representative of that index is unnecessary. -/
theorem supportMember_definable (hp : B.real.Definable L p.codes)
    (hq : q.IsDefinable L B.real) {U R : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hR : ImaginaryBaseFamilies.Relation (L := L) p B q R) (n : ℕ) :
    Predicate (L := L) p B q (fun a : Fin 2 → J => SupportMember U R n (a 0) (a 1)) := by
  let S := Fin 2 ⊕ Fin n
  have hs := ImaginaryTupleFormulas.reindex hp hq.1 (supportsTuple_definable hp hq.1 hU hR n)
    (Fin.cases (.inl 0) (fun i => .inr i) : Fin (n+1) → S)
  have he := ImaginaryTupleFormulas.exists_finite hp (fun i : Fin n =>
    coordinate_eq hp hq (Sum.inr i : S) (Sum.inl 1 : S))
  have hd := ImaginaryTupleFormulas.exists_block (ImaginaryTupleFormulas.inter hp hs he)
  unfold Predicate at hd ⊢
  convert hd using 1
  congr 1

theorem supportMember_eq_family (U R : J → Set M) (n : ℕ) (j : J) :
    {k | SupportMember U R n j k} = SupportFormulas.SupportFamily U (R j) n := by
  classical
  ext k
  constructor
  · rintro ⟨b,hb,hk⟩
    refine ⟨b,?_,hk⟩
    simpa only [Fin.cases_zero,Fin.cases_succ] using
      (supportsTuple_iff U R n (Fin.cases j b)).mp hb
  · rintro ⟨b,hb,hk⟩
    refine ⟨b,?_,hk⟩
    apply (supportsTuple_iff U R n (Fin.cases j b)).mpr
    simpa only [Fin.cases_zero,Fin.cases_succ] using hb

theorem supportMember_iff_canonical {balls : Set (Set M)} {U R : J → Set M}
    (hinj : Function.Injective U) (hl : IsLaminar balls) (htop : (Set.univ : Set M) ∈ balls)
    (hnf : MinimalBallSupport.AvoidsFiniteProperSubballs balls)
    (hU : ∀ j, U j ∈ balls) {j : J} {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport balls F (R j))
    (hcover : ∀ b ∈ F, ∃ k, U k = b) (k : J) :
    SupportMember U R F.card j k ↔ U k ∈ F := by
  have he := (supportMember_eq_family U R F.card j).trans
    (SupportFormulas.supportFamily_eq_preimage hinj hl htop hnf hF hU hcover)
  exact Set.ext_iff.mp he k

end IntegrationInACVF.Section3.FibreSupportFormulas
