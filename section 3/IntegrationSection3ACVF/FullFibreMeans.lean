import IntegrationSection3ACVF.FullFibreEnumerations
import Section3.FiniteFibreMeans

/-! Definability of actual finite-fibre means over a full interpreted base.
The enumeration and mean equation are first-order formulas; no centre or
enumeration is added to the base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.RawClosure.Tuple
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullFibreMeans

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def equation (k : ℕ) : Set (Fin 1 ⊕ Fin k → M) :=
  {w | iVF (w (.inl 0)) ∧
    @Term.realize LRV M (CanonicalStructure.normalize (M := M)) _ w (Barycentre.linearTerm k) = iVFZero}

theorem equation_definable (B : FullBaseAtomicity.Base (M := M)) (k : ℕ) :
    FullBaseAtomicity.OverBase B (equation k) := by
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hSort := FullBaseAtomicity.OverBase.preimage_comp
    (FullBaseAtomicity.OverBase.of_real (B := B) hs)
    (fun _ : Fin 1 => (Sum.inl 0 : Fin 1 ⊕ Fin k))
  have heq := @Barycentre.linearTerm_zero_definable M (@CanonicalStructure.normalize M sM) B.real k
  have hz : @iVFZero M (@CanonicalStructure.normalize M sM) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  rw [hz] at heq
  exact FullBaseAtomicity.OverBase.inter hSort (FullBaseAtomicity.OverBase.of_real heq)

def graphAt (F : (Fin n → M) → Finset (VFType (M := M))) (k : ℕ) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ c : Fin k → M, Enumerates (Barycentre.finiteFibreRelation F) k (z ∘ Sum.inl) c ∧
    Sum.elim (fun _ : Fin 1 => z (.inr 0)) c ∈ equation k}

theorem graphAt_definable (B : FullBaseAtomicity.Base (M := M))
    (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B
      {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ Barycentre.finiteFibreRelation F})
    (k : ℕ) : FullBaseAtomicity.OverBase B (graphAt F k) := by
  let ι := Fin n ⊕ Fin 1
  have hEnum := FullFibreEnumerations.definable B (Barycentre.finiteFibreRelation F) hF k
  have hE := FullBaseAtomicity.OverBase.preimage_comp hEnum
    (Sum.elim (fun i : Fin n => (Sum.inl (.inl i) : ι ⊕ Fin k)) Sum.inr)
  have hM := FullBaseAtomicity.OverBase.preimage_comp (equation_definable B k)
    (Sum.elim (fun _ : Fin 1 => (Sum.inl (.inr 0) : ι ⊕ Fin k)) Sum.inr)
  apply FullBaseAtomicity.OverBase.congr
    (FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hE hM))
  intro z
  simp only [graphAt,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_inter_iff,
    Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  apply exists_congr
  intro c
  apply and_congr
  · rfl
  · apply iff_of_eq
    congr 1
    funext i
    cases i <;> rfl

theorem normalized_mean_equation (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M))) (t : Fin n → M)
    {k : ℕ} (hk : k ≠ 0) (c : Fin k → M)
    (hc : Enumerates (Barycentre.finiteFibreRelation F) k t c) (mu : VFType (M := M)) :
    Sum.elim (fun _ : Fin 1 => mu.val) c ∈ equation k ↔ mu = Barycentre.mean (F t) := by
  have hsort (i : Fin k) : iVF (c i) := by
    obtain ⟨x,_,he⟩ := hc.2.1 i
    change x.val = c i at he
    exact he ▸ x.property
  have hn := CanonicalStructure.term_normalize hM (fun _ : Fin 1 => .vf) (fun _ : Fin k => .vf)
    (fun _ => mu.val) c (fun _ => mu.property) hsort (Barycentre.linearTerm k)
    (Barycentre.linearTerm_sorted k)
  change (iVF mu.val ∧ _) ↔ _
  rw [and_iff_right mu.property,hn]
  exact Barycentre.enumerated_mean_equation h00 F t hk c hc mu

theorem graphAt_value (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M))) {k : ℕ} (hk : k ≠ 0)
    {z : Fin n ⊕ Fin 1 → M} (hz : z ∈ graphAt F k) :
    z (.inr 0) = (Barycentre.mean (F (z ∘ Sum.inl))).val := by
  obtain ⟨c,hc,heq⟩ := hz
  let mu : VFType (M := M) := ⟨z (.inr 0),heq.1⟩
  exact congrArg Subtype.val ((normalized_mean_equation h00 F (z ∘ Sum.inl) hk c hc mu).mp heq)

theorem mean_mem_graphAt (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M))) (t : Fin n → M)
    (hk : (F t).card ≠ 0) :
    Sum.elim t ![(Barycentre.mean (F t)).val] ∈ graphAt F (F t).card := by
  obtain ⟨c,hc⟩ := Barycentre.finiteFibre_enumeration_exists F t
  refine ⟨c,hc,?_⟩
  exact (normalized_mean_equation h00 F t hk c hc (Barycentre.mean (F t))).mpr rfl

theorem bounded_graph_definable (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B
      {z : Fin n ⊕ Fin 1 → M | (z ∘ Sum.inl,z (.inr 0)) ∈ Barycentre.finiteFibreRelation F})
    (T : Set (Fin n → M)) (hT : FullBaseAtomicity.OverBase B T)
    (hne : ∀ t ∈ T, (F t).Nonempty) (N : ℕ) (hBound : ∀ t ∈ T, (F t).card ≤ N) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      z ∘ Sum.inl ∈ T ∧ z (.inr 0) = (Barycentre.mean (F (z ∘ Sum.inl))).val} := by
  have hRows (k : Fin (N+1)) : FullBaseAtomicity.OverBase B
      {z : Fin n ⊕ Fin 1 → M | k.val ≠ 0 ∧ z ∈ graphAt F k.val} := by
    by_cases hk : k.val = 0
    · have he : FullBaseAtomicity.OverBase B (∅ : Set (Fin n ⊕ Fin 1 → M)) := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact Set.definable_empty
      apply FullBaseAtomicity.OverBase.congr he
      intro z
      simp only [Set.mem_empty_iff_false,Set.mem_ofPred_eq,hk,ne_eq,not_true_eq_false,false_and]
    · apply FullBaseAtomicity.OverBase.congr (graphAt_definable B F hF k.val)
      intro z
      exact (and_iff_right hk).symm
  have hAny := FullFibreEnumerations.exists_finite B _ hRows
  have hDom := FullBaseAtomicity.OverBase.preimage_comp hT (Sum.inl : Fin n → Fin n ⊕ Fin 1)
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hDom hAny)
  intro z
  change ((z ∘ Sum.inl ∈ T) ∧ ∃ k : Fin (N+1), k.val ≠ 0 ∧ z ∈ graphAt F k.val) ↔
    (z ∘ Sum.inl ∈ T ∧ z (.inr 0) = (Barycentre.mean (F (z ∘ Sum.inl))).val)
  constructor
  · rintro ⟨ht,k,hk,hz⟩
    exact ⟨ht,graphAt_value h00 F hk hz⟩
  · rintro ⟨ht,hmu⟩
    have hk : (F (z ∘ Sum.inl)).card ≠ 0 := Finset.card_ne_zero.mpr (hne _ ht)
    let k : Fin (N+1) := ⟨(F (z ∘ Sum.inl)).card,Nat.lt_succ_of_le (hBound _ ht)⟩
    refine ⟨ht,k,hk,?_⟩
    have he : z = Sum.elim (z ∘ Sum.inl) ![(Barycentre.mean (F (z ∘ Sum.inl))).val] := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => fin_cases i; exact hmu
    rw [he]
    exact mean_mem_graphAt h00 F _ hk

end IntegrationInACVF.Section3ACVF.FullFibreMeans
