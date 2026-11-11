import IntegrationSection4.FullBaseMeans
import IntegrationSection3ACVF.RVDifferencePairs
import Section3.RawBarycentricCode

/-! Intrinsic barycentric RV codes for finite VF families over the full
original interpreted base. The combinatorial separation theorem is reused;
all means and intermediate RV values remain quantified in graph definitions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FullBaseFiniteCodes

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def head {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (t : Fin n → M) (x : M) : M := RVDifferencePairs.difference x (Barycentre.mean (F t)).val

theorem head_eq {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (t : Fin n → M) (x : VFType (M := M)) : head F t x.val = iRv (x-Barycentre.mean (F t)).val :=
  RVDifferencePairs.difference_vf x (Barycentre.mean (F t))

def code : (d : ℕ) → {n : ℕ} → ((Fin n → M) → Finset (VFType (M := M))) →
    (Fin n → M) → M → Fin d → M
  | 0,_,_,_,_ => Fin.elim0
  | d+1,_,F,t,x => Fin.cons (head F t x)
      (code d (Barycentre.childFamily F) (Fin.snoc t (head F t x)) x)

theorem head_graph (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ t, (F t).card ≤ N) :
    FullBaseFunctions.Graph B (fun w : Fin n ⊕ Fin 1 → M => head F (w ∘ Sum.inl) (w (.inr 0))) := by
  have hMean := FullBaseMeans.mean_graph B h00 F hF N hN
  have hM : FullBaseFunctions.Graph B (fun w : Fin n ⊕ Fin 1 → M => (Barycentre.mean (F (w ∘ Sum.inl))).val) :=
    FullBaseFunctions.comp B (g := fun w : Fin n ⊕ Fin 1 → M => w ∘ Sum.inl) hMean
      (fun i => FullBaseFunctions.projection B (Sum.inl i : Fin n ⊕ Fin 1))
  have hDiff : FullBaseFunctions.Graph B (fun w : Fin 2 → M => RVDifferencePairs.difference (w 0) (w 1)) :=
    FullBaseAtomicity.OverBase.preimage_comp (RVDifferencePairs.difference_graph_definable B)
      (![.inl 0,.inl 1,.inr 0] : Fin 3 → Fin 2 ⊕ Fin 1)
  apply FullBaseFunctions.comp B (g := fun w : Fin n ⊕ Fin 1 → M => ![w (.inr 0),(Barycentre.mean (F (w ∘ Sum.inl))).val]) hDiff
  intro i
  fin_cases i
  · exact FullBaseFunctions.projection B (Sum.inr 0 : Fin n ⊕ Fin 1)
  · exact hM

theorem child_graph (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ t, (F t).card ≤ N) :
    FullBaseAtomicity.OverBase B {z : Fin (n+1) ⊕ Fin 1 → M |
      ∃ x ∈ Barycentre.childFamily F (z ∘ Sum.inl), x.val = z (.inr 0)} := by
  let π : Fin n ⊕ Fin 1 → Fin (n+1) ⊕ Fin 1 := Sum.map Fin.castSucc id
  have hParent := FullBaseAtomicity.OverBase.preimage_comp hF π
  let ρ : (Fin n ⊕ Fin 1) ⊕ Fin 1 → Fin (n+1) ⊕ Fin 1 :=
    Sum.elim (Sum.elim (fun i => .inl i.castSucc) (fun _ => .inr 0)) (fun _ => .inl (Fin.last n))
  have hHead := FullBaseAtomicity.OverBase.preimage_comp (head_graph B h00 F hF N hN) ρ
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hParent hHead)
  intro z
  change ((∃ x ∈ F (Fin.init (z ∘ Sum.inl)), x.val = z (.inr 0)) ∧
    z (.inl (Fin.last n)) = head F (Fin.init (z ∘ Sum.inl)) (z (.inr 0))) ↔
      ∃ x ∈ Barycentre.childFamily F (z ∘ Sum.inl), x.val = z (.inr 0)
  constructor
  · rintro ⟨⟨x,hx,he⟩,hh⟩
    refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,he⟩
    rw [← he,head_eq] at hh
    exact hh.symm
  · rintro ⟨x,hx,he⟩
    obtain ⟨hx,hh⟩ := Finset.mem_filter.mp hx
    refine ⟨⟨x,hx,he⟩,?_⟩
    rw [← he,head_eq]
    exact hh.symm

theorem code_graph (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (d : ℕ) {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ t, (F t).card ≤ N) (i : Fin d) :
    FullBaseFunctions.Graph B (fun w : Fin n ⊕ Fin 1 → M => code d F (w ∘ Sum.inl) (w (.inr 0)) i) := by
  induction d generalizing n F with
  | zero => exact i.elim0
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact head_graph B h00 F hF N hN
    · have hChild := child_graph B h00 F hF N hN
      have hc := ih (Barycentre.childFamily F) hChild (Barycentre.childFamily_card_le F N hN) j
      let g (w : Fin n ⊕ Fin 1 → M) : Fin (n+1) ⊕ Fin 1 → M :=
        Sum.elim (Fin.snoc (w ∘ Sum.inl) (head F (w ∘ Sum.inl) (w (.inr 0)))) (fun _ => w (.inr 0))
      apply FullBaseFunctions.comp B (g := g) hc
      intro k
      cases k with
      | inl k =>
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simpa only [g,Sum.elim_inl,Fin.snoc_last] using head_graph B h00 F hF N hN
        · simpa only [g,Sum.elim_inl,Fin.snoc_castSucc,Function.comp_apply] using FullBaseFunctions.projection B (Sum.inl i : Fin n ⊕ Fin 1)
      | inr k => exact FullBaseFunctions.projection B (Sum.inr 0 : Fin n ⊕ Fin 1)

theorem code_eq_code (d : ℕ) {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (t : Fin n → M) (x : VFType (M := M)) : code d F t x.val = Barycentre.code d (F t) x := by
  induction d generalizing n F t with
  | zero => rfl
  | succ d ih =>
    rw [code,Barycentre.code,ih,head_eq]
    congr 1
    congr 1
    simp only [Barycentre.childFamily,Barycentre.fibre,Fin.init_snoc,Fin.snoc_last]

theorem code_sorted (d : ℕ) {n : ℕ} (F : (Fin n → M) → Finset (VFType (M := M)))
    (t : Fin n → M) (x : VFType (M := M)) (i : Fin d) : iRV (code d F t x.val i) := by
  rw [code_eq_code]
  exact Barycentre.code_sorted d (F t) x i

theorem code_injective (h00 : M ⊨ Axioms.ACVF00) (N : ℕ) {n : ℕ}
    (F : (Fin n → M) → Finset (VFType (M := M))) (hN : ∀ t, (F t).card ≤ N) (t : Fin n → M) :
    Set.InjOn (fun x : VFType (M := M) => code N F t x.val) (F t : Set (VFType (M := M))) := by
  intro x hx y hy he
  change code N F t x.val = code N F t y.val at he
  rw [@code_eq_code M sM hM N n F t x,@code_eq_code M sM hM N n F t y] at he
  exact Barycentre.code_injective_of_card_le h00 N (F t) ((hN t).trans (Nat.le_succ N)) hx hy he

end IntegrationInACVF.Section4.FullBaseFiniteCodes
