module

public import IntegrationSection3.HoleFormulas

@[expose] public section

/-! Equality and images of real-code sets in a faithful interpreted family.
All valid representatives are quantified, retaining the original base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.SupportFormulas
open IntegrationInACVF.Section3.HoleFormulas

namespace IntegrationInACVF.Section3.CodeEquality

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def EqualityCodes (q : Presentation M J η) (U : J → Set M) :
    Set (Fin 2 × η → M) :=
  {c | c ∈ tupleCodes q (Fin 2) ∧ ∀ t : Fin 1 → M,
    row c 0 (t 0) ∈ q.relationPullback U ↔ row c 1 (t 0) ∈ q.relationPullback U}

theorem equalityCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U) :
    OverBase (L := L) p B (EqualityCodes q U) := by
  let π (i : Fin 2) : η ⊕ Fin 1 → (Fin 2 × η) ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (i,a)) Sum.inr
  have hm (i : Fin 2) := OverBase.preimage_comp hU (π i)
  have hall := OverBase.forall_block (iff_definable hp (hm 0) (hm 1)) hp
  have hc := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin 2))
  convert OverBase.inter hc hall hp using 1
  ext c
  have he (t : Fin 1 → M) (i : Fin 2) : Sum.elim c t ∘ π i = row c i (t 0) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  change (c ∈ tupleCodes q (Fin 2) ∧ ∀ t : Fin 1 → M,
      row c 0 (t 0) ∈ q.relationPullback U ↔ row c 1 (t 0) ∈ q.relationPullback U) ↔
    (c ∈ tupleCodes q (Fin 2) ∧ ∀ t : Fin 1 → M,
      Sum.elim c t ∘ π 0 ∈ q.relationPullback U ↔ Sum.elim c t ∘ π 1 ∈ q.relationPullback U)
  simp only [he]

omit [L.Structure M] [Finite η] in
theorem pairRows_mem_iff {U : J → Set M} (a b : q.codes) :
    pairRows a.val b.val ∈ EqualityCodes q U ↔ U (q.decode a) = U (q.decode b) := by
  have hc : pairRows a.val b.val ∈ tupleCodes q (Fin 2) := by
    intro i
    fin_cases i
    · exact a.property
    · exact b.property
  change (pairRows a.val b.val ∈ tupleCodes q (Fin 2) ∧ ∀ t : Fin 1 → M,
    row (pairRows a.val b.val) 0 (t 0) ∈ q.relationPullback U ↔
      row (pairRows a.val b.val) 1 (t 0) ∈ q.relationPullback U) ↔ _
  constructor
  · intro h
    ext x
    exact (q.mem_relationPullback U a x).symm.trans ((h.2 ![x]).trans (q.mem_relationPullback U b x))
  · intro he
    refine ⟨hc,fun t => ?_⟩
    exact (q.mem_relationPullback U a (t 0)).trans
      ((Set.ext_iff.mp he (t 0)).trans (q.mem_relationPullback U b (t 0)).symm)

def imageCodes (q : Presentation M J η) (A : Set (η → M)) : Set J :=
  {j | ∃ a ∈ A, ∃ ha : a ∈ q.codes, q.decode ⟨a,ha⟩ = j}

theorem imageCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hinj : Function.Injective U) {A : Set (η → M)}
    (hA : OverBase (L := L) p B A) :
    ImaginaryBaseFamilies.Family (L := L) p B q (imageCodes q A) := by
  let π : Fin 2 × η → η ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl a) i
  have heq := (equalityCodes_definable hp hq hU).preimage_comp π
  have ha := hA.preimage_comp (Sum.inr : η → η ⊕ η)
  have hex := OverBase.exists_block (OverBase.inter ha heq hp)
  have hc := OverBase.of_real (p := p) (B := B) hq
  change OverBase (L := L) p B (q.pullback (imageCodes q A))
  convert OverBase.inter hc hex hp using 1
  ext c
  have hep (d : η → M) : Sum.elim c d ∘ π = pairRows d c := by
    funext (i,a)
    fin_cases i <;> rfl
  change (∃ hc : c ∈ q.codes, ∃ d ∈ A, ∃ hd : d ∈ q.codes, q.decode ⟨d,hd⟩ = q.decode ⟨c,hc⟩) ↔
    (c ∈ q.codes ∧ ∃ d : η → M, d ∈ A ∧ Sum.elim c d ∘ π ∈ EqualityCodes q U)
  simp only [hep]
  constructor
  · rintro ⟨hc,d,hdA,hd,he⟩
    exact ⟨hc,d,hdA,(pairRows_mem_iff ⟨d,hd⟩ ⟨c,hc⟩).mpr (congrArg U he)⟩
  · rintro ⟨hc,d,hdA,he⟩
    have hd : d ∈ q.codes := he.1 0
    exact ⟨hc,d,hdA,hd,hinj ((pairRows_mem_iff ⟨d,hd⟩ ⟨c,hc⟩).mp he)⟩

def imageCodeRelation (q : Presentation M J η) (A : Set (η ⊕ Fin 1 → M)) (j : J) : Set M :=
  {x | ∃ a : q.codes, Sum.elim a.val ![x] ∈ A ∧ q.decode a = j}

theorem imageCodeRelation_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    (hinj : Function.Injective U) {A : Set (η ⊕ Fin 1 → M)}
    (hA : OverBase (L := L) p B A) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (imageCodeRelation q A) := by
  let πE : Fin 2 × η → (η ⊕ Fin 1) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl (.inl a)) i
  let πA : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ η :=
    Sum.elim Sum.inr (fun i => .inl (.inr i))
  have heq := (equalityCodes_definable hp hq hU).preimage_comp πE
  have ha := hA.preimage_comp πA
  have hex := OverBase.exists_block (OverBase.inter ha heq hp)
  change OverBase (L := L) p B (q.relationPullback (imageCodeRelation q A))
  convert hex using 1
  ext z
  have he (d : η → M) : Sum.elim z d ∘ πE = pairRows d (z ∘ Sum.inl) := by
    funext (i,a)
    fin_cases i <;> rfl
  have ha (d : η → M) : Sum.elim z d ∘ πA = Sum.elim d ![z (.inr 0)] := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i; rfl
  change (∃ hc : z ∘ Sum.inl ∈ q.codes, ∃ a : q.codes,
      Sum.elim a.val ![z (.inr 0)] ∈ A ∧ q.decode a = q.decode ⟨z ∘ Sum.inl,hc⟩) ↔
    ∃ d : η → M, Sum.elim z d ∘ πA ∈ A ∧ Sum.elim z d ∘ πE ∈ EqualityCodes q U
  simp only [he,ha]
  constructor
  · rintro ⟨hc,a,hA,he⟩
    exact ⟨a.val,hA,(pairRows_mem_iff a ⟨z ∘ Sum.inl,hc⟩).mpr (congrArg U he)⟩
  · rintro ⟨d,hA,he⟩
    have hd : d ∈ q.codes := he.1 0
    have hc : z ∘ Sum.inl ∈ q.codes := he.1 1
    exact ⟨hc,⟨d,hd⟩,hA,hinj ((pairRows_mem_iff ⟨d,hd⟩ ⟨z ∘ Sum.inl,hc⟩).mp he)⟩


end IntegrationInACVF.Section3.CodeEquality
