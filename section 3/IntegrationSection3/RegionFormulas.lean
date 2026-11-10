module

public import IntegrationSection3.SupportFormulas
public import IntegrationSection3.PuncturedDecomposition

@[expose] public section

/-! Full-code formulas for containment and positive regions in an interpreted
family of sets. Every quantified code and the original parameter base are
retained; no representative or finite enumeration is named. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.SupportFormulas

namespace IntegrationInACVF.Section3.RegionFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def StrictSubsetCodes (q : Presentation M J η) (U : J → Set M) :
    Set (Fin 2 × η → M) :=
  {c | c ∈ tupleCodes q (Fin 2) ∧
    (∀ t : Fin 1 → M, row c 0 (t 0) ∈ q.relationPullback U → row c 1 (t 0) ∈ q.relationPullback U) ∧
    ∃ t : Fin 1 → M, row c 1 (t 0) ∈ q.relationPullback U ∧ row c 0 (t 0) ∉ q.relationPullback U}

theorem strictSubsetCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U) :
    OverBase (L := L) p B (StrictSubsetCodes q U) := by
  let π (i : Fin 2) : η ⊕ Fin 1 → (Fin 2 × η) ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (i,a)) Sum.inr
  have hm (i : Fin 2) := OverBase.preimage_comp hU (π i)
  have hall := OverBase.forall_block (imp_definable hp (hm 0) (hm 1)) hp
  have hex := OverBase.exists_block (OverBase.inter (hm 1) (OverBase.compl (hm 0) hp) hp)
  have hc := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin 2))
  convert OverBase.inter hc (OverBase.inter hall hex hp) hp using 1
  ext c
  have he (t : Fin 1 → M) (i : Fin 2) : Sum.elim c t ∘ π i = row c i (t 0) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  change (c ∈ tupleCodes q (Fin 2) ∧
      (∀ t : Fin 1 → M, row c 0 (t 0) ∈ q.relationPullback U → row c 1 (t 0) ∈ q.relationPullback U) ∧
      ∃ t : Fin 1 → M, row c 1 (t 0) ∈ q.relationPullback U ∧ row c 0 (t 0) ∉ q.relationPullback U) ↔
    (c ∈ tupleCodes q (Fin 2) ∧
      (∀ t : Fin 1 → M, Sum.elim c t ∘ π 0 ∈ q.relationPullback U →
        Sum.elim c t ∘ π 1 ∈ q.relationPullback U) ∧
      ∃ t : Fin 1 → M, Sum.elim c t ∘ π 1 ∈ q.relationPullback U ∧
        Sum.elim c t ∘ π 0 ∉ q.relationPullback U)
  simp only [he]

omit [Finite η] in
theorem mem_strictSubsetCodes_iff {U : J → Set M}
    (c : Fin 2 × η → M) (hc : c ∈ tupleCodes q (Fin 2)) :
    c ∈ StrictSubsetCodes q U ↔
      U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ⊂ U (q.decode ⟨(fun j => c (1,j)),hc 1⟩) := by
  have hm (i : Fin 2) (x : M) : row c i x ∈ q.relationPullback U ↔
      x ∈ U (q.decode ⟨(fun j => c (i,j)),hc i⟩) :=
    q.mem_relationPullback U ⟨(fun j => c (i,j)),hc i⟩ x
  constructor
  · rintro ⟨_,ha,he⟩
    refine ⟨fun x hx => (hm 1 x).mp (ha ![x] ((hm 0 x).mpr hx)),?_⟩
    intro hrev
    obtain ⟨t,ht1,ht0⟩ := he
    exact ht0 ((hm 0 (t 0)).mpr (hrev ((hm 1 (t 0)).mp ht1)))
  · intro hs
    refine ⟨hc,fun t ht => (hm 1 (t 0)).mpr (hs.1 ((hm 0 (t 0)).mp ht)),?_⟩
    obtain ⟨x,hx1,hx0⟩ := Set.not_subset.mp hs.2
    exact ⟨![x],(hm 1 x).mpr hx1,fun hx => hx0 ((hm 0 x).mp hx)⟩


def regionFamily (T : Set J) (U : J → Set M) (j : J) : Set M :=
  {x | x ∈ U j ∧ ¬ ∃ k ∈ T, U k ⊂ U j ∧ x ∈ U k}

theorem regionFamily_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (regionFamily T U) := by
  let πS : Fin 2 × η → (η ⊕ Fin 1) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl (.inl a)) i
  let πM : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ η :=
    Sum.elim Sum.inr (fun i => .inl (.inr i))
  have hs := (strictSubsetCodes_definable hp hq hU).preimage_comp πS
  have hm := OverBase.preimage_comp hU πM
  have ht := OverBase.preimage_comp hT (Sum.inr : η → (η ⊕ Fin 1) ⊕ η)
  have hb := OverBase.exists_block (OverBase.inter ht (OverBase.inter hs hm hp) hp)
  change OverBase (L := L) p B (q.relationPullback (regionFamily T U))
  convert OverBase.inter hU (OverBase.compl hb hp) hp using 1
  ext z
  have hmcomp (c : η → M) : Sum.elim z c ∘ πM = Sum.elim c ![z (.inr 0)] := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  have hbad (hz : z ∘ Sum.inl ∈ q.codes) :
      (∃ c : η → M, c ∈ q.pullback T ∧
        Sum.elim z c ∘ πS ∈ StrictSubsetCodes q U ∧
        Sum.elim z c ∘ πM ∈ q.relationPullback U) ↔
      ∃ k ∈ T, U k ⊂ U (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧ z (.inr 0) ∈ U k := by
    constructor
    · rintro ⟨c,⟨hc,hct⟩,hcs,hcm⟩
      have hsub := (mem_strictSubsetCodes_iff (Sum.elim z c ∘ πS) hcs.1).mp hcs
      have hs' : U (q.decode ⟨c,hc⟩) ⊂ U (q.decode ⟨z ∘ Sum.inl,hz⟩) := hsub
      rw [hmcomp] at hcm
      exact ⟨q.decode ⟨c,hc⟩,hct,hs',
        (q.mem_relationPullback U ⟨c,hc⟩ (z (.inr 0))).mp hcm⟩
    · rintro ⟨k,hk,hsub,hxk⟩
      obtain ⟨c,hck⟩ := q.onto k
      have hcode : Sum.elim z c.val ∘ πS ∈ tupleCodes q (Fin 2) := by
        intro i
        fin_cases i
        · exact c.property
        · exact hz
      have hcs : Sum.elim z c.val ∘ πS ∈ StrictSubsetCodes q U := by
        apply (mem_strictSubsetCodes_iff _ hcode).mpr
        change U (q.decode c) ⊂ U (q.decode ⟨z ∘ Sum.inl,hz⟩)
        rw [hck]
        exact hsub
      refine ⟨c.val,⟨c.property,?_⟩,hcs,?_⟩
      · change q.decode c ∈ T
        rw [hck]
        exact hk
      · rw [hmcomp]
        apply (q.mem_relationPullback U c (z (.inr 0))).mpr
        rw [hck]
        exact hxk
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      z (.inr 0) ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧
        ¬ ∃ k ∈ T, U k ⊂ U (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧ z (.inr 0) ∈ U k) ↔
    ((∃ hz : z ∘ Sum.inl ∈ q.codes, z (.inr 0) ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩)) ∧
      ¬ ∃ c : η → M, c ∈ q.pullback T ∧
        Sum.elim z c ∘ πS ∈ StrictSubsetCodes q U ∧
        Sum.elim z c ∘ πM ∈ q.relationPullback U)
  constructor
  · rintro ⟨hz,hx,hn⟩
    exact ⟨⟨hz,hx⟩,fun h => hn ((hbad hz).mp h)⟩
  · rintro ⟨⟨hz,hx⟩,hn⟩
    exact ⟨hz,hx,fun h => hn ((hbad hz).mpr h)⟩


theorem family_compl (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {T : Set J}
    (hT : ImaginaryBaseFamilies.Family (L := L) p B q T) :
    ImaginaryBaseFamilies.Family (L := L) p B q Tᶜ := by
  change OverBase (L := L) p B (q.pullback Tᶜ)
  convert OverBase.inter (OverBase.of_real (p := p) (B := B) hq) (OverBase.compl hT hp) hp using 1
  ext c
  change (∃ hc : c ∈ q.codes, q.decode ⟨c,hc⟩ ∉ T) ↔
    (c ∈ q.codes ∧ ¬ ∃ hc : c ∈ q.codes, q.decode ⟨c,hc⟩ ∈ T)
  exact ⟨fun ⟨hc,hn⟩ => ⟨hc,fun ⟨_,ht⟩ => hn ht⟩,
    fun ⟨hc,hn⟩ => ⟨hc,fun ht => hn ⟨hc,ht⟩⟩⟩

theorem constantRelation (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {A : Set M}
    (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A}) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (fun _ => A) := by
  have hc := (OverBase.of_real (p := p) (B := B) hq).preimage_comp
    (Sum.inl : η → η ⊕ Fin 1)
  have ha := hA.preimage_comp (Sum.inr : Fin 1 → η ⊕ Fin 1)
  change OverBase (L := L) p B (q.relationPullback (fun _ => A))
  convert OverBase.inter hc ha hp using 1
  ext z
  change (∃ hz : z ∘ Sum.inl ∈ q.codes, z (.inr 0) ∈ A) ↔
    (z ∘ Sum.inl ∈ q.codes ∧ z (.inr 0) ∈ A)
  exact ⟨fun ⟨hz,ha⟩ => ⟨hz,ha⟩,fun ⟨hz,ha⟩ => ⟨hz,ha⟩⟩

def positiveFamily (T : Set J) (U : J → Set M) (A : Set M) : Set J :=
  {j | j ∈ T ∧ (regionFamily T U j).Nonempty ∧ regionFamily T U j ⊆ A}

theorem positiveFamily_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    {A : Set M} (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A}) :
    ImaginaryBaseFamilies.Family (L := L) p B q (positiveFamily T U A) := by
  have hr := regionFamily_definable hp hq hU hT
  have hd := ImaginaryBaseFamilies.Relation.domain hr
  have hout := ImaginaryBaseFamilies.Relation.inter hp hr
    (constantRelation (A := Aᶜ) hp hq (OverBase.compl hA hp))
  have hn := family_compl hp hq (ImaginaryBaseFamilies.Relation.domain hout)
  have h := ImaginaryBaseFamilies.Family.inter hp hT (ImaginaryBaseFamilies.Family.inter hp hd hn)
  have he : positiveFamily T U A = T ∩
      ({j | (regionFamily T U j).Nonempty} ∩ {j | (regionFamily T U j ∩ Aᶜ).Nonempty}ᶜ) := by
    ext j
    change (j ∈ T ∧ (regionFamily T U j).Nonempty ∧ regionFamily T U j ⊆ A) ↔
      (j ∈ T ∧ (regionFamily T U j).Nonempty ∧ ¬ (regionFamily T U j ∩ Aᶜ).Nonempty)
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    constructor
    · intro hsub hb
      obtain ⟨x,hx,hxn⟩ := hb
      exact hxn (hsub hx)
    · intro hn x hx
      by_contra hxn
      exact hn ⟨x,hx,hxn⟩
  rw [he]
  exact h

omit [L.Structure M] [Finite η] in
theorem regionFamily_eq_region {U : J → Set M} {F : Finset (Set M)}
    (hcover : ∀ b ∈ F, ∃ k, U k = b) (j : J) :
    regionFamily (U ⁻¹' (F : Set (Set M))) U j =
      PuncturedDecomposition.region F (U j) := by
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx,fun b hb hbj hxb => ?_⟩
    obtain ⟨k,hk⟩ := hcover b hb
    apply hn
    refine ⟨k,?_,?_,?_⟩
    · change U k ∈ F
      rwa [hk]
    · rwa [hk]
    · rwa [hk]
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun ⟨k,hk,hkj,hxk⟩ => hn (U k) hk hkj hxk⟩

omit [L.Structure M] [Finite η] in
theorem positiveFamily_eq_preimage {U : J → Set M} {F : Finset (Set M)}
    (hcover : ∀ b ∈ F, ∃ k, U k = b) (A : Set M) :
    positiveFamily (U ⁻¹' (F : Set (Set M))) U A =
      U ⁻¹' {b | b ∈ F ∧ (PuncturedDecomposition.region F b).Nonempty ∧
        PuncturedDecomposition.region F b ⊆ A} := by
  ext j
  change (U j ∈ F ∧ (regionFamily _ U j).Nonempty ∧ regionFamily _ U j ⊆ A) ↔ _
  rw [regionFamily_eq_region hcover j]
  rfl

omit [L.Structure M] [Finite η] in
theorem positive_regions_cover {balls : Set (Set M)} (hl : IsLaminar balls)
    {F : Finset (Set M)} (hF : ∀ b ∈ F, b ∈ balls) {A : Set M}
    (hs : MinimalBallSupport.Supports F A)
    (hcover : ∀ x ∈ A, ∃ b ∈ F, x ∈ b) :
    A = {x | ∃ b ∈ F, (PuncturedDecomposition.region F b).Nonempty ∧
      PuncturedDecomposition.region F b ⊆ A ∧ x ∈ PuncturedDecomposition.region F b} := by
  ext x
  constructor
  · intro hx
    obtain ⟨d,hd,hxd⟩ := hcover x hx
    obtain ⟨b,hb,hxb⟩ := PuncturedDecomposition.exists_region hd hxd
    refine ⟨b,hb,⟨x,hxb⟩,?_,hxb⟩
    intro y hy
    exact (hs x y (PuncturedDecomposition.region_agreement hl hF hb hxb hy)).mp hx
  · rintro ⟨b,_,_,hsub,hxb⟩
    exact hsub hxb

end IntegrationInACVF.Section3.RegionFormulas
