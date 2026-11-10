module

public import IntegrationSection3.HoleFormulas

@[expose] public section

/-! Inclusion and fixed-family enlargement through all interpreted codes.
No parent, hole or enlargement is individually named in the base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.SupportFormulas
open IntegrationInACVF.Section3.RegionFormulas
open IntegrationInACVF.Section3.HoleFormulas

namespace IntegrationInACVF.Section3.BallInclusionFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def SubsetCodes (q : Presentation M J η) (U : J → Set M) :
    Set (Fin 2 × η → M) :=
  {c | c ∈ tupleCodes q (Fin 2) ∧
    ∀ t : Fin 1 → M, row c 0 (t 0) ∈ q.relationPullback U →
      row c 1 (t 0) ∈ q.relationPullback U}

theorem subsetCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U) :
    OverBase (L := L) p B (SubsetCodes q U) := by
  let π (i : Fin 2) : η ⊕ Fin 1 → (Fin 2 × η) ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (i,a)) Sum.inr
  have hall := OverBase.forall_block
    (imp_definable hp (hU.preimage_comp (π 0)) (hU.preimage_comp (π 1))) hp
  have hc := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin 2))
  convert OverBase.inter hc hall hp using 1
  ext c
  have he (t : Fin 1 → M) (i : Fin 2) : Sum.elim c t ∘ π i = row c i (t 0) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  change (c ∈ tupleCodes q (Fin 2) ∧
      ∀ t : Fin 1 → M, row c 0 (t 0) ∈ q.relationPullback U →
        row c 1 (t 0) ∈ q.relationPullback U) ↔
    (c ∈ tupleCodes q (Fin 2) ∧
      ∀ t : Fin 1 → M, Sum.elim c t ∘ π 0 ∈ q.relationPullback U →
        Sum.elim c t ∘ π 1 ∈ q.relationPullback U)
  simp only [he]

omit [L.Structure M] [Finite η] in
theorem mem_subsetCodes_iff {U : J → Set M}
    (c : Fin 2 × η → M) (hc : c ∈ tupleCodes q (Fin 2)) :
    c ∈ SubsetCodes q U ↔
      U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ⊆ U (q.decode ⟨(fun j => c (1,j)),hc 1⟩) := by
  have hm (i : Fin 2) (x : M) : row c i x ∈ q.relationPullback U ↔
      x ∈ U (q.decode ⟨(fun j => c (i,j)),hc i⟩) :=
    q.mem_relationPullback U ⟨(fun j => c (i,j)),hc i⟩ x
  exact ⟨fun h x hx => (hm 1 x).mp (h.2 ![x] ((hm 0 x).mpr hx)),
    fun h => ⟨hc,fun t ht => (hm 1 (t 0)).mpr (h ((hm 0 (t 0)).mp ht))⟩⟩

/-- Row zero is an old hole from C, row one its parent, and row two
an enlargement from D lying properly inside that parent. -/
theorem enlargement_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {C D : Set J} (hC : ImaginaryBaseFamilies.Family (L := L) p B q C)
    (hD : ImaginaryBaseFamilies.Family (L := L) p B q D) :
    OverBase (L := L) p B ((tuplePresentation q (Fin 3)).pullback
      {a | a 0 ∈ C ∧ a 2 ∈ D ∧ U (a 0) ⊆ U (a 2) ∧ U (a 2) ⊂ U (a 1)}) := by
  let πlo : Fin 2 × η → Fin 3 × η :=
    fun (i,a) => Fin.cases (0,a) (fun _ => (2,a)) i
  let πhi : Fin 2 × η → Fin 3 × η :=
    fun (i,a) => Fin.cases (2,a) (fun _ => (1,a)) i
  have hc := hC.preimage_comp (fun a => ((0 : Fin 3),a))
  have hd := hD.preimage_comp (fun a => ((2 : Fin 3),a))
  have hlo := (subsetCodes_definable hp hq hU).preimage_comp πlo
  have hhi := (strictSubsetCodes_definable hp hq hU).preimage_comp πhi
  have hv := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin 3))
  convert OverBase.inter hv (OverBase.inter hc
    (OverBase.inter hd (OverBase.inter hlo hhi hp) hp) hp) hp using 1
  ext c
  have he (hvalid : c ∈ tupleCodes q (Fin 3)) :
      (c ∘ πlo ∈ SubsetCodes q U ∧ c ∘ πhi ∈ StrictSubsetCodes q U) ↔
        U (q.decode ⟨(fun a => c (0,a)),hvalid 0⟩) ⊆
          U (q.decode ⟨(fun a => c (2,a)),hvalid 2⟩) ∧
        U (q.decode ⟨(fun a => c (2,a)),hvalid 2⟩) ⊂
          U (q.decode ⟨(fun a => c (1,a)),hvalid 1⟩) := by
    have hvlo : c ∘ πlo ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact hvalid 0
      · exact hvalid 2
    have hvhi : c ∘ πhi ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact hvalid 2
      · exact hvalid 1
    exact and_congr (mem_subsetCodes_iff _ hvlo) (mem_strictSubsetCodes_iff _ hvhi)
  change (∃ hv : c ∈ tupleCodes q (Fin 3),
      q.decode ⟨(fun a => c (0,a)),hv 0⟩ ∈ C ∧
      q.decode ⟨(fun a => c (2,a)),hv 2⟩ ∈ D ∧
      U (q.decode ⟨(fun a => c (0,a)),hv 0⟩) ⊆ U (q.decode ⟨(fun a => c (2,a)),hv 2⟩) ∧
      U (q.decode ⟨(fun a => c (2,a)),hv 2⟩) ⊂ U (q.decode ⟨(fun a => c (1,a)),hv 1⟩)) ↔
    (c ∈ tupleCodes q (Fin 3) ∧
      (fun a => c (0,a)) ∈ q.pullback C ∧ (fun a => c (2,a)) ∈ q.pullback D ∧
        c ∘ πlo ∈ SubsetCodes q U ∧ c ∘ πhi ∈ StrictSubsetCodes q U)
  constructor
  · rintro ⟨hv,hc,hd,hlo,hhi⟩
    exact ⟨hv,⟨hv 0,hc⟩,⟨hv 2,hd⟩,(he hv).mpr ⟨hlo,hhi⟩⟩
  · rintro ⟨hv,⟨_,hc⟩,⟨_,hd⟩,hlo,hhi⟩
    exact ⟨hv,hc,hd,(he hv).mp ⟨hlo,hhi⟩⟩

end IntegrationInACVF.Section3.BallInclusionFormulas
