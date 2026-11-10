module

public import IntegrationSection3.HoleFormulas

@[expose] public section

/-! Quantifying over full hole codes. The graph may be produced by a
definable transformation of the original holes; it need not enumerate them
or choose a centre. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.HoleFormulas

namespace IntegrationInACVF.Section3.PunctureFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

/-- The first argument of R is the hole, the second its parent. -/
def puncturedFamily (R : J → J → Prop) (U : J → Set M) (j : J) : Set M :=
  {x | x ∈ U j ∧ ¬ ∃ k, R k j ∧ x ∈ U k}

theorem puncturedFamily_definable (hp : B.real.Definable L p.codes)
    {U : J → Set M} (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {R : J → J → Prop}
    (hR : OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)})) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (puncturedFamily R U) := by
  let πR : Fin 2 × η → (η ⊕ Fin 1) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl (.inl a)) i
  let πU : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ η :=
    Sum.elim Sum.inr (fun i => .inl (.inr i))
  have hr := hR.preimage_comp πR
  have hu := OverBase.preimage_comp hU πU
  have hd := OverBase.exists_block (OverBase.inter hr hu hp)
  change OverBase (L := L) p B (q.relationPullback (puncturedFamily R U))
  convert OverBase.inter hU (OverBase.compl hd hp) hp using 1
  ext z
  have heR (c : η → M) : Sum.elim z c ∘ πR = pairRows c (z ∘ Sum.inl) := by
    funext (i,a)
    fin_cases i <;> rfl
  have heU (c : η → M) : Sum.elim z c ∘ πU = Sum.elim c ![z (.inr 0)] := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  have hbad (hz : z ∘ Sum.inl ∈ q.codes) :
      (∃ c : η → M,
        Sum.elim z c ∘ πR ∈
          (tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)} ∧
        Sum.elim z c ∘ πU ∈ q.relationPullback U) ↔
      ∃ k, R k (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧ z (.inr 0) ∈ U k := by
    constructor
    · rintro ⟨c,hcR,hcU⟩
      rw [heR] at hcR
      rw [heU] at hcU
      obtain ⟨hc,hx⟩ := hcU
      refine ⟨q.decode ⟨c,hc⟩,?_,hx⟩
      exact hcR.2
    · rintro ⟨k,hk,hx⟩
      obtain ⟨c,hck⟩ := q.onto k
      refine ⟨c.val,?_,?_⟩
      · rw [heR]
        have hv : pairRows c.val (z ∘ Sum.inl) ∈ tupleCodes q (Fin 2) := by
          intro i
          fin_cases i
          · exact c.property
          · exact hz
        refine ⟨hv,?_⟩
        change R (q.decode c) (q.decode ⟨z ∘ Sum.inl,hz⟩)
        rwa [hck]
      · rw [heU]
        apply (q.mem_relationPullback U c (z (.inr 0))).mpr
        rwa [hck]
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      z (.inr 0) ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧
        ¬ ∃ k, R k (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧ z (.inr 0) ∈ U k) ↔
    ((∃ hz : z ∘ Sum.inl ∈ q.codes, z (.inr 0) ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩)) ∧
      ¬ ∃ c : η → M, Sum.elim z c ∘ πR ∈
        (tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)} ∧
        Sum.elim z c ∘ πU ∈ q.relationPullback U)
  constructor
  · rintro ⟨hz,hx,hn⟩
    exact ⟨⟨hz,hx⟩,fun h => hn ((hbad hz).mp h)⟩
  · rintro ⟨⟨hz,hx⟩,hn⟩
    exact ⟨hz,hx,fun h => hn ((hbad hz).mpr h)⟩

/-- An enlargement graph E takes an old hole, its parent and a new hole. -/
def transported (R : J → J → Prop) (E : J → J → J → Prop) (k j : J) : Prop :=
  ∃ h, R h j ∧ E h j k

theorem transported_definable (hp : B.real.Definable L p.codes)
    {R : J → J → Prop} {E : J → J → J → Prop}
    (hR : OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)}))
    (hE : OverBase (L := L) p B
      ((tuplePresentation q (Fin 3)).pullback {a | E (a 0) (a 1) (a 2)})) :
    OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | transported R E (a 0) (a 1)}) := by
  let πR : Fin 2 × η → (Fin 2 × η) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl (1,a)) i
  let πE : Fin 3 × η → (Fin 2 × η) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a)
      (fun i => Fin.cases (.inl (1,a)) (fun _ => .inl (0,a)) i) i
  have hd := OverBase.exists_block
    (OverBase.inter (hR.preimage_comp πR) (hE.preimage_comp πE) hp)
  convert hd using 1
  ext z
  change (∃ hz : z ∈ tupleCodes q (Fin 2),
      ∃ h, R h (q.decode ⟨(fun a => z (1,a)),hz 1⟩) ∧
        E h (q.decode ⟨(fun a => z (1,a)),hz 1⟩)
          (q.decode ⟨(fun a => z (0,a)),hz 0⟩)) ↔
    ∃ c : η → M,
      Sum.elim z c ∘ πR ∈ (tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)} ∧
      Sum.elim z c ∘ πE ∈ (tuplePresentation q (Fin 3)).pullback
        {a | E (a 0) (a 1) (a 2)}
  constructor
  · rintro ⟨hz,h,hhR,hhE⟩
    obtain ⟨c,hch⟩ := q.onto h
    have hcR : Sum.elim z c.val ∘ πR ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact c.property
      · exact hz 1
    have hcE : Sum.elim z c.val ∘ πE ∈ tupleCodes q (Fin 3) := by
      intro i
      fin_cases i
      · exact c.property
      · exact hz 1
      · exact hz 0
    refine ⟨c.val,⟨hcR,?_⟩,⟨hcE,?_⟩⟩
    · change R (q.decode c) (q.decode ⟨(fun a => z (1,a)),hz 1⟩)
      rwa [hch]
    · change E (q.decode c) (q.decode ⟨(fun a => z (1,a)),hz 1⟩)
        (q.decode ⟨(fun a => z (0,a)),hz 0⟩)
      rwa [hch]
  · rintro ⟨c,⟨hcR,hhR⟩,⟨hcE,hhE⟩⟩
    have hz : z ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact hcE 2
      · exact hcE 1
    refine ⟨hz,q.decode ⟨c,hcR 0⟩,hhR,hhE⟩

/-- Retain all old holes while adjoining every enlargement from E.
The union is taken on the interpreted graph, through every real code. -/
theorem add_transport_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes)
    {R : J → J → Prop} {E : J → J → J → Prop}
    (hR : OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)}))
    (hE : OverBase (L := L) p B
      ((tuplePresentation q (Fin 3)).pullback {a | E (a 0) (a 1) (a 2)})) :
    OverBase (L := L) p B ((tuplePresentation q (Fin 2)).pullback
      {a | R (a 0) (a 1) ∨ transported R E (a 0) (a 1)}) := by
  have ht := transported_definable hp hR hE
  have hqt := tupleCodes_definable hq (Fin 2)
  have hd := RegionFormulas.family_compl hp hqt
    (ImaginaryBaseFamilies.Family.inter hp
      (RegionFormulas.family_compl hp hqt hR)
      (RegionFormulas.family_compl hp hqt ht))
  change OverBase (L := L) p B
    ((tuplePresentation q (Fin 2)).pullback
      ({a | R (a 0) (a 1)}ᶜ ∩ {a | transported R E (a 0) (a 1)}ᶜ)ᶜ) at hd
  convert hd using 1
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,Set.mem_inter_iff,not_and_or,not_not]

end IntegrationInACVF.Section3.PunctureFormulas
