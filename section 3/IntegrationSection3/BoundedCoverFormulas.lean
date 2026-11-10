module

public import IntegrationSection3.BallInclusionFormulas
public import IntegrationSection3.CoarsePartition

@[expose] public section

/-! A fixed finite bound on proper-ball covers is first-order definable
through all codes. Zero holes are permitted, so empty preimage pieces and
singleton parents do not require a padding convention. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.SupportFormulas
open IntegrationInACVF.Section3.RegionFormulas
open IntegrationInACVF.Section3.HoleFormulas

namespace IntegrationInACVF.Section3.BoundedCoverFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def CoverWitness (q : Presentation M J η) (U C : J → Set M) (n : ℕ) :
    Set ((Fin 2 × η) ⊕ (Fin n × η) → M) :=
  {z | z ∘ Sum.inl ∈ tupleCodes q (Fin 2) ∧ z ∘ Sum.inr ∈ tupleCodes q (Fin n) ∧
    (∀ i : Fin n, pairRows (fun a => z (.inr (i,a))) (fun a => z (.inl (0,a))) ∈
      StrictSubsetCodes q U) ∧
    ∀ t : Fin 1 → M, row (z ∘ Sum.inl) 1 (t 0) ∈ q.relationPullback C →
      ∃ i : Fin n, row (z ∘ Sum.inr) i (t 0) ∈ q.relationPullback U}

theorem coverWitness_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) (n : ℕ) :
    OverBase (L := L) p B (CoverWitness q U C n) := by
  let β := (Fin 2 × η) ⊕ (Fin n × η)
  let πS (i : Fin n) : Fin 2 × η → β :=
    fun (k,a) => Fin.cases (.inr (i,a)) (fun _ => .inl (0,a)) k
  let πC : η ⊕ Fin 1 → β ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (.inl (1,a))) Sum.inr
  let πU (i : Fin n) : η ⊕ Fin 1 → β ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (.inr (i,a))) Sum.inr
  have hc := (OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin 2))).preimage_comp
    (Sum.inl : Fin 2 × η → β)
  have hh := (OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin n))).preimage_comp
    (Sum.inr : Fin n × η → β)
  have hs := OverBase.forall_finite
    (fun i : Fin n => (strictSubsetCodes_definable hp hq hU).preimage_comp (πS i)) hp
  have hm := exists_finite hp (fun i : Fin n => hU.preimage_comp (πU i))
  have hall := OverBase.forall_block (imp_definable hp (hC.preimage_comp πC) hm) hp
  convert OverBase.inter hc (OverBase.inter hh (OverBase.inter hs hall hp) hp) hp using 1
  ext z
  have heS (i : Fin n) : z ∘ πS i =
      pairRows (fun a => z (.inr (i,a))) (fun a => z (.inl (0,a))) := by
    funext (k,a)
    fin_cases k <;> rfl
  have heC (t : Fin 1 → M) : Sum.elim z t ∘ πC = row (z ∘ Sum.inl) 1 (t 0) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  have heU (t : Fin 1 → M) (i : Fin n) :
      Sum.elim z t ∘ πU i = row (z ∘ Sum.inr) i (t 0) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  change (z ∘ Sum.inl ∈ tupleCodes q (Fin 2) ∧ z ∘ Sum.inr ∈ tupleCodes q (Fin n) ∧
      (∀ i : Fin n, pairRows (fun a => z (.inr (i,a))) (fun a => z (.inl (0,a))) ∈
        StrictSubsetCodes q U) ∧
      ∀ t : Fin 1 → M, row (z ∘ Sum.inl) 1 (t 0) ∈ q.relationPullback C →
        ∃ i : Fin n, row (z ∘ Sum.inr) i (t 0) ∈ q.relationPullback U) ↔
    (z ∘ Sum.inl ∈ tupleCodes q (Fin 2) ∧ z ∘ Sum.inr ∈ tupleCodes q (Fin n) ∧
      (∀ i : Fin n, z ∘ πS i ∈ StrictSubsetCodes q U) ∧
      ∀ t : Fin 1 → M, Sum.elim z t ∘ πC ∈ q.relationPullback C →
        ∃ i : Fin n, Sum.elim z t ∘ πU i ∈ q.relationPullback U)
  simp only [heS,heC,heU]

def TupleCover (U C : J → Set M) (n : ℕ) (a : Fin 2 → J) : Prop :=
  ∃ h : Fin n → J, (∀ i, U (h i) ⊂ U (a 0)) ∧ C (a 1) ⊆ {x | ∃ i, x ∈ U (h i)}

theorem tupleCover_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) (n : ℕ) :
    OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | TupleCover U C n a}) := by
  have hd := OverBase.exists_block (coverWitness_definable hp hq hU hC n)
  convert hd using 1
  ext c
  change (∃ hc : c ∈ tupleCodes q (Fin 2),
      ∃ h : Fin n → J,
        (∀ i, U (h i) ⊂ U (q.decode ⟨(fun a => c (0,a)),hc 0⟩)) ∧
        C (q.decode ⟨(fun a => c (1,a)),hc 1⟩) ⊆ {x | ∃ i, x ∈ U (h i)}) ↔
    ∃ d : Fin n × η → M, Sum.elim c d ∈ CoverWitness q U C n
  constructor
  · rintro ⟨hc,h,hproper,hcov⟩
    obtain ⟨d,hdh⟩ := (tuplePresentation q (Fin n)).onto h
    have he (i : Fin n) : q.decode ⟨(fun a => d.val (i,a)),d.property i⟩ = h i :=
      congrFun hdh i
    refine ⟨d.val,hc,d.property,?_,?_⟩
    · intro i
      apply (pairRows_mem_iff
        (⟨fun a => d.val (i,a),d.property i⟩ : q.codes)
        (⟨fun a => c (0,a),hc 0⟩ : q.codes)).mpr
      rw [he]
      exact hproper i
    · intro t ht
      have hx : t 0 ∈ C (q.decode ⟨(fun a => c (1,a)),hc 1⟩) :=
        (q.mem_relationPullback C ⟨(fun a => c (1,a)),hc 1⟩ (t 0)).mp ht
      obtain ⟨i,hi⟩ := hcov hx
      refine ⟨i,?_⟩
      apply (q.mem_relationPullback U ⟨(fun a => d.val (i,a)),d.property i⟩ (t 0)).mpr
      rwa [he]
  · rintro ⟨d,hc,hd,hproper,hcov⟩
    let h := (tuplePresentation q (Fin n)).decode ⟨d,hd⟩
    refine ⟨hc,h,?_,?_⟩
    · intro i
      exact (pairRows_mem_iff
        (⟨fun a => d (i,a),hd i⟩ : q.codes)
        (⟨fun a => c (0,a),hc 0⟩ : q.codes)).mp (hproper i)
    · intro x hx
      have ht := hcov ![x]
        ((q.mem_relationPullback C ⟨(fun a => c (1,a)),hc 1⟩ x).mpr hx)
      obtain ⟨i,hi⟩ := ht
      exact ⟨i,(q.mem_relationPullback U ⟨(fun a => d (i,a)),hd i⟩ x).mp hi⟩

def AtMostCover (U C : J → Set M) (N : ℕ) (a : Fin 2 → J) : Prop :=
  ∃ n : Fin (N+1), TupleCover U C n.val a

theorem atMostCover_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) (N : ℕ) :
    OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | AtMostCover U C N a}) := by
  have hd := exists_finite hp (fun n : Fin (N+1) => tupleCover_definable hp hq hU hC n.val)
  convert hd using 1
  ext c
  change (∃ hc : c ∈ tupleCodes q (Fin 2), ∃ n : Fin (N+1),
      TupleCover U C n.val ((tuplePresentation q (Fin 2)).decode ⟨c,hc⟩)) ↔
    ∃ n : Fin (N+1), ∃ hc : c ∈ tupleCodes q (Fin 2),
      TupleCover U C n.val ((tuplePresentation q (Fin 2)).decode ⟨c,hc⟩)
  exact exists_comm

omit [L.Structure M] [Finite η] in
/-- With complete coverage by actual ball names, the first-order tuple
test is exactly finite covering by at most N proper balls. Repeated names
are harmless; the finite disjunction includes the empty tuple. -/
theorem atMostCover_iff {balls : Set (Set M)} {U C : J → Set M}
    (hU : ∀ j, U j ∈ balls) (hballs : ∀ b ∈ balls, ∃ j, U j = b)
    (i j : J) (N : ℕ) :
    AtMostCover U C N ![i,j] ↔ CoarsePartition.CoveredBy balls (U i) (C j) N := by
  classical
  constructor
  · rintro ⟨n,h,hproper,hcov⟩
    let H := Finset.univ.image (fun k => U (h k))
    have hcard : H.card ≤ N := by
      calc
        H.card ≤ (Finset.univ : Finset (Fin n.val)).card := Finset.card_image_le
        _ = n.val := by simp
        _ ≤ N := Nat.le_of_lt_succ n.isLt
    refine ⟨H,hcard,?_,?_⟩
    · intro b hb
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hb
      exact ⟨hU (h k),hproper k⟩
    · intro x hx
      obtain ⟨k,hk⟩ := hcov hx
      exact ⟨U (h k),Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,hk⟩
  · rintro ⟨H,hcard,hH,hcov⟩
    let e : Fin H.card ≃ H := H.equivFin.symm
    choose h ht using fun k : Fin H.card => hballs (e k).val (hH _ (e k).property).1
    refine ⟨⟨H.card,Nat.lt_succ_of_le hcard⟩,h,?_,?_⟩
    · intro k
      change U (h k) ⊂ U i
      rw [ht k]
      exact (hH _ (e k).property).2
    · intro x hx
      obtain ⟨b,hb,hxb⟩ := hcov hx
      let k := e.symm ⟨b,hb⟩
      have he : (e k).val = b := congrArg Subtype.val (e.apply_symm_apply ⟨b,hb⟩)
      refine ⟨k,?_⟩
      rw [ht k,he]
      exact hxb

theorem uncoveredFamily_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U C : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    {P T : Set J} (hP : ImaginaryBaseFamilies.Family (L := L) p B q P)
    (hT : ImaginaryBaseFamilies.Family (L := L) p B q T) (N : ℕ) :
    ImaginaryBaseFamilies.Family (L := L) p B q
      {j | j ∈ T ∧ ∃ i ∈ P, ¬ AtMostCover U C N ![i,j]} := by
  have hc := atMostCover_definable hp hq hU hC N
  have hn := family_compl hp (tupleCodes_definable hq (Fin 2)) hc
  have hp0 := hP.preimage_comp (fun a : η => ((0 : Fin 2),a))
  have ht1 := hT.preimage_comp (fun a : η => ((1 : Fin 2),a))
  have hd : OverBase (L := L) p B ((tuplePresentation q (Fin 2)).pullback
      {a | a 0 ∈ P ∧ a 1 ∈ T ∧ ¬ AtMostCover U C N a}) := by
    convert OverBase.inter hn (OverBase.inter hp0 ht1 hp) hp using 1
    ext c
    change (∃ hc : c ∈ tupleCodes q (Fin 2),
        q.decode ⟨(fun a => c (0,a)),hc 0⟩ ∈ P ∧
        q.decode ⟨(fun a => c (1,a)),hc 1⟩ ∈ T ∧
        ¬ AtMostCover U C N ((tuplePresentation q (Fin 2)).decode ⟨c,hc⟩)) ↔
      ((∃ hc : c ∈ tupleCodes q (Fin 2),
        ¬ AtMostCover U C N ((tuplePresentation q (Fin 2)).decode ⟨c,hc⟩)) ∧
        (fun a => c (0,a)) ∈ q.pullback P ∧ (fun a => c (1,a)) ∈ q.pullback T)
    exact ⟨fun ⟨hc,hi,hj,hn⟩ => ⟨⟨hc,hn⟩,⟨hc 0,hi⟩,⟨hc 1,hj⟩⟩,
      fun ⟨⟨hc,hn⟩,⟨_,hi⟩,⟨_,hj⟩⟩ => ⟨hc,hi,hj,hn⟩⟩
  have hproj := ImaginaryBaseFamilies.pair_domain hd
  convert hproj using 1
  ext j
  change (j ∈ T ∧ ∃ i ∈ P, ¬ AtMostCover U C N ![i,j]) ↔
    ∃ i, i ∈ P ∧ j ∈ T ∧ ¬ AtMostCover U C N ![i,j]
  exact ⟨fun ⟨hj,i,hi,hn⟩ => ⟨i,hi,hj,hn⟩,
    fun ⟨i,hi,hj,hn⟩ => ⟨hj,i,hi,hn⟩⟩

end IntegrationInACVF.Section3.BoundedCoverFormulas
