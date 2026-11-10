module

public import IntegrationSection3.RegionFormulas

@[expose] public section

/-! Full-code definability of the maximal-hole relation in a support family.
A hole is proper in its parent and has no strictly intermediate support ball.
The semantic identification uses only coverage by the interpreted family. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.RegionFormulas

namespace IntegrationInACVF.Section3.HoleFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def pairRows (a b : η → M) : Fin 2 × η → M :=
  fun (i,j) => Fin.cases (a j) (fun _ => b j) i

/-- Row zero is a maximal proper member of T below row one. -/
def HoleCodes (q : Presentation M J η) (T : Set J) (U : J → Set M) :
    Set (Fin 2 × η → M) :=
  {c | c ∈ StrictSubsetCodes q U ∧ (fun j => c (0,j)) ∈ q.pullback T ∧
    ¬ ∃ d : η → M, d ∈ q.pullback T ∧
      pairRows (fun j => c (0,j)) d ∈ StrictSubsetCodes q U ∧
      pairRows d (fun j => c (1,j)) ∈ StrictSubsetCodes q U}

theorem holeCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {T : Set J} (hT : ImaginaryBaseFamilies.Family (L := L) p B q T) :
    OverBase (L := L) p B (HoleCodes q T U) := by
  let πlo : Fin 2 × η → (Fin 2 × η) ⊕ η :=
    fun (i,a) => Fin.cases (.inl (0,a)) (fun _ => .inr a) i
  let πhi : Fin 2 × η → (Fin 2 × η) ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl (1,a)) i
  have hs := strictSubsetCodes_definable hp hq hU
  have hlo := hs.preimage_comp πlo
  have hhi := hs.preimage_comp πhi
  have ht := hT.preimage_comp (Sum.inr : η → (Fin 2 × η) ⊕ η)
  have hex := OverBase.exists_block (OverBase.inter ht (OverBase.inter hlo hhi hp) hp)
  have ht0 := hT.preimage_comp (fun a : η => ((0 : Fin 2),a))
  convert OverBase.inter hs (OverBase.inter ht0 (OverBase.compl hex hp) hp) hp using 1
  ext c
  have helo (d : η → M) : Sum.elim c d ∘ πlo = pairRows (fun a => c (0,a)) d := by
    funext (i,a)
    fin_cases i <;> rfl
  have hehi (d : η → M) : Sum.elim c d ∘ πhi = pairRows d (fun a => c (1,a)) := by
    funext (i,a)
    fin_cases i <;> rfl
  change (c ∈ StrictSubsetCodes q U ∧ (fun j => c (0,j)) ∈ q.pullback T ∧
      ¬ ∃ d : η → M, d ∈ q.pullback T ∧
        pairRows (fun j => c (0,j)) d ∈ StrictSubsetCodes q U ∧
        pairRows d (fun j => c (1,j)) ∈ StrictSubsetCodes q U) ↔
    (c ∈ StrictSubsetCodes q U ∧ (fun j => c (0,j)) ∈ q.pullback T ∧
      ¬ ∃ d : η → M, d ∈ q.pullback T ∧
        Sum.elim c d ∘ πlo ∈ StrictSubsetCodes q U ∧
        Sum.elim c d ∘ πhi ∈ StrictSubsetCodes q U)
  simp only [helo,hehi]

omit [L.Structure M] [Finite η] in
theorem pairRows_mem_iff {U : J → Set M} (a b : q.codes) :
    pairRows a.val b.val ∈ StrictSubsetCodes q U ↔ U (q.decode a) ⊂ U (q.decode b) := by
  have hc : pairRows a.val b.val ∈ tupleCodes q (Fin 2) := by
    intro i
    fin_cases i
    · exact a.property
    · exact b.property
  exact mem_strictSubsetCodes_iff _ hc

omit [L.Structure M] [Finite η] in
theorem mem_holeCodes_iff {U : J → Set M} {T : Set J}
    (c : Fin 2 × η → M) (hc : c ∈ tupleCodes q (Fin 2)) :
    c ∈ HoleCodes q T U ↔
      q.decode ⟨(fun j => c (0,j)),hc 0⟩ ∈ T ∧
      U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ⊂ U (q.decode ⟨(fun j => c (1,j)),hc 1⟩) ∧
      ¬ ∃ k ∈ T, U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ⊂ U k ∧
        U k ⊂ U (q.decode ⟨(fun j => c (1,j)),hc 1⟩) := by
  let a : q.codes := ⟨fun j => c (0,j),hc 0⟩
  let b : q.codes := ⟨fun j => c (1,j),hc 1⟩
  have ht : (fun j => c (0,j)) ∈ q.pullback T ↔ q.decode a ∈ T := by
    exact q.mem_pullback T a
  have hi : (∃ d : η → M, d ∈ q.pullback T ∧
      pairRows a.val d ∈ StrictSubsetCodes q U ∧ pairRows d b.val ∈ StrictSubsetCodes q U) ↔
      ∃ k ∈ T, U (q.decode a) ⊂ U k ∧ U k ⊂ U (q.decode b) := by
    constructor
    · rintro ⟨d,⟨hd,hdt⟩,hlo,hhi⟩
      exact ⟨q.decode ⟨d,hd⟩,hdt,(pairRows_mem_iff a ⟨d,hd⟩).mp hlo,
        (pairRows_mem_iff ⟨d,hd⟩ b).mp hhi⟩
    · rintro ⟨k,hk,hlo,hhi⟩
      obtain ⟨d,hd⟩ := q.onto k
      refine ⟨d.val,⟨d.property,?_⟩,(pairRows_mem_iff a d).mpr ?_,(pairRows_mem_iff d b).mpr ?_⟩
      · rwa [hd]
      · rwa [hd]
      · rwa [hd]
  change (c ∈ StrictSubsetCodes q U ∧ a.val ∈ q.pullback T ∧ ¬ _) ↔ _
  rw [mem_strictSubsetCodes_iff c hc,ht,hi]
  exact and_left_comm

omit [L.Structure M] [Finite η] in
theorem maximal_iff_mem_holes {U : J → Set M} {F : Finset (Set M)}
    (hcover : ∀ b ∈ F, ∃ k, U k = b) (j k : J) :
    (U k ∈ F ∧ U k ⊂ U j ∧ ¬ ∃ l, U l ∈ F ∧ U k ⊂ U l ∧ U l ⊂ U j) ↔
      U k ∈ PuncturedDecomposition.holes F (U j) := by
  rw [PuncturedDecomposition.mem_holes]
  constructor
  · rintro ⟨hk,hsub,hn⟩
    refine ⟨hk,hsub,fun d hd hdj hkd => ?_⟩
    by_contra hdk
    obtain ⟨l,hl⟩ := hcover d hd
    apply hn
    refine ⟨l,?_,?_,?_⟩
    · rwa [hl]
    · rw [hl]
      exact ⟨hkd,hdk⟩
    · rwa [hl]
  · rintro ⟨hk,hsub,hmax⟩
    refine ⟨hk,hsub,?_⟩
    rintro ⟨l,hl,hkl,hlj⟩
    exact hkl.2 (hmax (U l) hl hlj hkl.1)

omit [L.Structure M] [Finite η] in
theorem holeCodes_eq_pullback {U : J → Set M} {F : Finset (Set M)}
    (hcover : ∀ b ∈ F, ∃ k, U k = b) :
    HoleCodes q (U ⁻¹' (F : Set (Set M))) U =
      (tuplePresentation q (Fin 2)).pullback
        {a | U (a 0) ∈ PuncturedDecomposition.holes F (U (a 1))} := by
  ext c
  have he (hc : c ∈ tupleCodes q (Fin 2)) :
      c ∈ HoleCodes q (U ⁻¹' (F : Set (Set M))) U ↔
      U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ∈
        PuncturedDecomposition.holes F (U (q.decode ⟨(fun j => c (1,j)),hc 1⟩)) := by
    rw [mem_holeCodes_iff c hc]
    exact maximal_iff_mem_holes hcover _ _
  change c ∈ HoleCodes q (U ⁻¹' (F : Set (Set M))) U ↔
    ∃ hc : c ∈ tupleCodes q (Fin 2),
      U (q.decode ⟨(fun j => c (0,j)),hc 0⟩) ∈
        PuncturedDecomposition.holes F (U (q.decode ⟨(fun j => c (1,j)),hc 1⟩))
  exact ⟨fun h => ⟨h.1.1,(he h.1.1).mp h⟩,fun ⟨hc,h⟩ => (he hc).mpr h⟩

end IntegrationInACVF.Section3.HoleFormulas
