module

public import IntegrationSection3.ImaginaryBaseFamilies
public import IntegrationSection3.SupportFormulas
public import Mathlib.Data.Set.Card

@[expose] public section

/-! Finite fibre counting over an unchanged interpreted base. Atomicity
of the input domain gives a uniform bound without saturation or cardinal
restrictions on the base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.AtomicFiniteFibres

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {B : Base M I}

def HasMore (R : Set (M × M)) (n : ℕ) : Set M :=
  {x | ∃ b : Fin (n+1) → M, Function.Injective b ∧ ∀ i, (x,b i) ∈ R}

/-- The finite count is an ordinary first-order formula, with all original
imaginary support retained. -/
theorem hasMore_definable (hp : B.real.Definable L p.codes)
    {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) (n : ℕ) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ HasMore R n} := by
  classical
  let α := Fin 1 ⊕ Fin (n+1)
  have hr := OverBase.forall_finite (fun i : Fin (n+1) =>
    hR.preimage_comp (![.inl 0,.inr i] : Fin 2 → α)) hp
  have hne (ij : Fin (n+1) × Fin (n+1)) :
      OverBase (L := L) p B {z : α → M | ij.1 = ij.2 ∨ z (.inr ij.1) ≠ z (.inr ij.2)} := by
    apply OverBase.of_real
    by_cases he : ij.1 = ij.2
    · simpa only [he,true_or,Set.ofPred_true] using
        (Set.definable_univ (L := L) (A := B.real) (α := α))
    · have heq : B.real.Definable L {z : α → M | z (.inr ij.1) = z (.inr ij.2)} :=
        ⟨(Language.Term.var (.inr ij.1)).equal (Language.Term.var (.inr ij.2)),rfl⟩
      simpa only [he,false_or,Set.compl_ofPred] using heq.compl
  have hd := OverBase.exists_block (OverBase.inter (OverBase.forall_finite hne hp) hr hp)
  convert hd using 1
  ext z
  change (∃ b : Fin (n+1) → M, Function.Injective b ∧ ∀ i, (z 0,b i) ∈ R) ↔
    ∃ b : Fin (n+1) → M,
      (∀ ij : Fin (n+1) × Fin (n+1), ij.1 = ij.2 ∨ b ij.1 ≠ b ij.2) ∧
        ∀ i, (z 0,b i) ∈ R
  constructor
  · rintro ⟨b,hb,hr⟩
    exact ⟨b,fun ij => or_iff_not_imp_left.mpr (fun he => hb.ne he),hr⟩
  · rintro ⟨b,hb,hr⟩
    exact ⟨b,fun i j he => (hb (i,j)).resolve_right (fun hne => hne he),hr⟩

omit [L.Structure M] in
theorem exists_injective_of_card_le {S : Set M} (hS : S.Finite) {n : ℕ} (hn : n ≤ S.ncard) :
    ∃ b : Fin n → M, Function.Injective b ∧ ∀ i, b i ∈ S := by
  classical
  obtain ⟨T,hTS,hcard⟩ := Set.exists_subset_card_eq hn
  have hT := hS.subset hTS
  have hc : hT.toFinset.card = n := by rw [← hcard,Set.ncard_eq_toFinset_card T hT]
  let e : ↥hT.toFinset ≃ Fin n := Finset.equivFinOfCardEq hc
  exact ⟨fun i => (e.symm i).val,
    fun i j he => e.symm.injective (Subtype.ext he),
    fun i => hTS (hT.mem_toFinset.mp (e.symm i).property)⟩

omit [L.Structure M] in
theorem not_hasMore_iff {R : Set (M × M)} (x : M) (n : ℕ)
    (hfin : {y | (x,y) ∈ R}.Finite) :
    x ∉ HasMore R n ↔ {y | (x,y) ∈ R}.ncard ≤ n := by
  constructor
  · intro hn
    apply le_of_not_gt
    intro hlt
    exact hn (exists_injective_of_card_le hfin (Nat.succ_le_of_lt hlt))
  · intro hle
    rintro ⟨b,hb,hr⟩
    have hc := Set.ncard_le_ncard_of_injOn b (fun i (_ : i ∈ (Set.univ : Set (Fin (n+1)))) => hr i)
      (fun i _ j _ he => hb he) hfin
    simp only [Set.ncard_univ,Nat.card_fin] at hc
    exact Nat.not_succ_le_self n (hc.trans hle)

theorem uniform_bound (hp : B.real.Definable L p.codes)
    {P : Set M} (hP : ImaginaryBaseFamilies.CompleteType (L := L) p B P)
    {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hfinite : ∀ x ∈ P, {y | (x,y) ∈ R}.Finite) :
    ∃ N : ℕ, ∀ x ∈ P, {y | (x,y) ∈ R}.ncard ≤ N := by
  classical
  by_cases hne : P.Nonempty
  · obtain ⟨x0,hx0⟩ := hne
    let N := {y | (x0,y) ∈ R}.ncard
    have hxN : x0 ∈ (HasMore R N)ᶜ := (not_hasMore_iff x0 N (hfinite x0 hx0)).mpr le_rfl
    have hd := OverBase.compl (hasMore_definable hp hR N) hp
    have hall : P ⊆ (HasMore R N)ᶜ := by
      rcases hP (HasMore R N)ᶜ hd with hall | hnone
      · exact hall
      · exact (Set.disjoint_left.mp hnone hx0 hxN).elim
    exact ⟨N,fun x hx => (not_hasMore_iff x N (hfinite x hx)).mp (hall hx)⟩
  · exact ⟨0,fun x hx => (hne ⟨x,hx⟩).elim⟩

end IntegrationInACVF.Section3.AtomicFiniteFibres
