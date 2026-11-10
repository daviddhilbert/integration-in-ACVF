module

public import IntegrationSection3.BallInclusionFormulas

@[expose] public section

/-! Intrinsic closed-cover radius predicates for canonical support
families. Parent and support balls are quantified through all codes. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.CoverRadiusFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def covers (U V : J → Set M) (D : Set J) (R : J → J → Prop) (j : J) : Set M :=
  {t | ∃ k ∈ D, t ∈ V k ∧ ∀ l, R j l → U l ⊆ U k}

theorem covers_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U V : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hV : ImaginaryBaseFamilies.Relation (L := L) p B q V)
    {D : Set J} (hD : ImaginaryBaseFamilies.Family (L := L) p B q D)
    {R : J → J → Prop}
    (hR : OverBase (L := L) p B
      ((tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)})) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (covers U V D R) := by
  let W := η ⊕ Fin 1
  let πR : Fin 2 × η → (W ⊕ η) ⊕ η := fun (i,e) =>
    Fin.cases (.inl (.inl (.inl e))) (fun _ => .inr e) i
  let πS : Fin 2 × η → (W ⊕ η) ⊕ η := fun (i,e) =>
    Fin.cases (.inr e) (fun _ => .inl (.inr e)) i
  let πV : η ⊕ Fin 1 → W ⊕ η :=
    Sum.elim Sum.inr (fun _ => .inl (.inr 0))
  have hforall := OverBase.forall_block (SupportFormulas.imp_definable hp
    (hR.preimage_comp πR) ((BallInclusionFormulas.subsetCodes_definable hp hq hU).preimage_comp πS)) hp
  have hd := hD.preimage_comp (Sum.inr : η → W ⊕ η)
  have hv := hV.preimage_comp πV
  have hex := OverBase.exists_block (OverBase.inter hd (OverBase.inter hv hforall hp) hp)
  have hguard := (OverBase.of_real (p := p) (B := B) hq).preimage_comp
    (Sum.inl : η → W)
  change OverBase (L := L) p B (q.relationPullback (covers U V D R))
  convert OverBase.inter hguard hex hp using 1
  ext z
  have heV (c : η → M) : Sum.elim z c ∘ πV = Sum.elim c ![z (.inr 0)] := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => fin_cases e; rfl
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      ∃ k ∈ D, z (.inr 0) ∈ V k ∧ ∀ l,
        R (q.decode ⟨z ∘ Sum.inl,hz⟩) l → U l ⊆ U k) ↔
    (z ∘ Sum.inl ∈ q.codes ∧ ∃ c : η → M,
      c ∈ q.pullback D ∧ Sum.elim z c ∘ πV ∈ q.relationPullback V ∧
        ∀ e : η → M,
          Sum.elim (Sum.elim z c) e ∘ πR ∈ (tuplePresentation q (Fin 2)).pullback
            {a | R (a 0) (a 1)} →
          Sum.elim (Sum.elim z c) e ∘ πS ∈ BallInclusionFormulas.SubsetCodes q U)
  simp only [heV]
  constructor
  · rintro ⟨hz,k,hk,hv,hcov⟩
    obtain ⟨c,hck⟩ := q.onto k
    refine ⟨hz,c.val,⟨c.property,?_⟩,?_,?_⟩
    · rwa [hck]
    · apply (q.mem_relationPullback V c (z (.inr 0))).mpr
      rwa [hck]
    · intro e he
      have hecode : e ∈ q.codes := he.1 1
      have hvalid : Sum.elim (Sum.elim z c.val) e ∘ πS ∈ tupleCodes q (Fin 2) := by
        intro i
        fin_cases i
        · exact hecode
        · exact c.property
      apply (BallInclusionFormulas.mem_subsetCodes_iff _ hvalid).mpr
      change U (q.decode ⟨e,hecode⟩) ⊆ U (q.decode c)
      rw [hck]
      apply hcov
      exact he.2
  · rintro ⟨hz,c,⟨hc,hcD⟩,hv,hall⟩
    have hv' := (q.mem_relationPullback V ⟨c,hc⟩ (z (.inr 0))).mp hv
    refine ⟨hz,q.decode ⟨c,hc⟩,hcD,hv',?_⟩
    intro l hl
    obtain ⟨e,hel⟩ := q.onto l
    have hvalidR : Sum.elim (Sum.elim z c) e.val ∘ πR ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact hz
      · exact e.property
    have hrel : Sum.elim (Sum.elim z c) e.val ∘ πR ∈
        (tuplePresentation q (Fin 2)).pullback {a | R (a 0) (a 1)} := by
      refine ⟨hvalidR,?_⟩
      change R (q.decode ⟨z ∘ Sum.inl,hz⟩) (q.decode e)
      rwa [hel]
    have hsubset := hall e.val hrel
    have heq := (BallInclusionFormulas.mem_subsetCodes_iff _ hsubset.1).mp hsubset
    change U (q.decode e) ⊆ U (q.decode ⟨c,hc⟩) at heq
    rwa [hel] at heq

def greatest (C : J → Set M) (le : Set (M × M)) (j : J) : Set M :=
  {t | t ∈ C j ∧ ∀ s ∈ C j, (s,t) ∈ le}

theorem greatest_definable (hp : B.real.Definable L p.codes)
    {C : J → Set M} (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    {le : Set (M × M)}
    (hle : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ le}) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (greatest C le) := by
  let πC : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun e => .inl (.inl e)) Sum.inr
  let πle : Fin 2 → (η ⊕ Fin 1) ⊕ Fin 1 := ![.inr 0,.inl (.inr 0)]
  have hall := OverBase.forall_block (SupportFormulas.imp_definable hp
    (hC.preimage_comp πC) (hle.preimage_comp πle)) hp
  change OverBase (L := L) p B (q.relationPullback (greatest C le))
  convert OverBase.inter hC hall hp using 1
  ext z
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      z (.inr 0) ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩) ∧
        ∀ s ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩), (s,z (.inr 0)) ∈ le) ↔
    ((∃ hz : z ∘ Sum.inl ∈ q.codes, z (.inr 0) ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩)) ∧
      ∀ s : Fin 1 → M,
        (∃ hz : z ∘ Sum.inl ∈ q.codes, s 0 ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩)) →
          (s 0,z (.inr 0)) ∈ le)
  constructor
  · rintro ⟨hz,ht,h⟩
    exact ⟨⟨hz,ht⟩,fun s ⟨_,hs⟩ => h (s 0) hs⟩
  · rintro ⟨⟨hz,ht⟩,h⟩
    exact ⟨hz,ht,fun s hs => h ![s] ⟨hz,hs⟩⟩

end IntegrationInACVF.Section3.CoverRadiusFormulas
