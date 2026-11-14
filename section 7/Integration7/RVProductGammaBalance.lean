import Integration7.RVTupleProductTerms
import Integration7.GammaDefinableTransforms

/-! A genuine first-order formula for equality of Gamma products on
nonzero RV tuples. It uses the native valuation preorder and the actual
RV product term; it does not identify RV classes of equal valuation. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rvProductGammaBalance (n : ℕ) : Set (Fin (n+n) → M) :=
  {w | Proper w ∧
    iLe ((rvTupleProductTerm n).realize (w ∘ Fin.castAdd n))
      ((rvTupleProductTerm n).realize (w ∘ Fin.natAdd n)) ∧
    iLe ((rvTupleProductTerm n).realize (w ∘ Fin.natAdd n))
      ((rvTupleProductTerm n).realize (w ∘ Fin.castAdd n))}

theorem rvProductGammaBalance_raw_definable (S : Set M) (n : ℕ) :
    S.Definable LRV (rvProductGammaBalance (M := M) n) := by
  let T := rvTupleProductTerm n
  have hL : S.DefinableFun LRV (fun w : Fin (n+n) → M => T.realize (w ∘ Fin.castAdd n)) :=
    (Set.DefinableFun.of_empty (T.definableFun_realize (M := M))).comp
      (show S.DefinableMap LRV (fun w : Fin (n+n) → M => w ∘ Fin.castAdd n) from
        fun _ => Set.DefinableFun.proj LRV)
  have hR : S.DefinableFun LRV (fun w : Fin (n+n) → M => T.realize (w ∘ Fin.natAdd n)) :=
    (Set.DefinableFun.of_empty (T.definableFun_realize (M := M))).comp
      (show S.DefinableMap LRV (fun w : Fin (n+n) → M => w ∘ Fin.natAdd n) from
        fun _ => Set.DefinableFun.proj LRV)
  have hLR := (raw_le_definable S).preimage_map
    (show S.DefinableMap LRV (fun w : Fin (n+n) → M =>
      ![T.realize (w ∘ Fin.castAdd n),T.realize (w ∘ Fin.natAdd n)]) from
        fun i => by fin_cases i; exact hL; exact hR)
  have hRL := (raw_le_definable S).preimage_map
    (show S.DefinableMap LRV (fun w : Fin (n+n) → M =>
      ![T.realize (w ∘ Fin.natAdd n),T.realize (w ∘ Fin.castAdd n)]) from
        fun i => by fin_cases i; exact hR; exact hL)
  have hP : S.Definable LRV {w : Fin (n+n) → M | Proper w} := by
    convert Set.definable_iInter_of_finite (fun i : Fin (n+n) =>
      (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i)) using 1
    ext w
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_preimage,Proper,Function.comp_apply]
    rfl
  exact hP.inter (hLR.inter hRL)

theorem rvProductGammaBalance_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) :
    DefinableOverBase B (fun _ : Fin (n+n) => .rv) (rvProductGammaBalance (M := M) n) := by
  let R := rvProductGammaBalance (M := M) n
  have hR : @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin (n+n)) R :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M (@Base.real M sM hM B) LRV I (Fin (n+n)) R)
      (normalize_eq_of_isCanonical hc).symm) (rvProductGammaBalance_raw_definable B.real n)
  apply real_definableOverBase B _ _
  apply (definableOver_iff_normalized_raw B.real _ _).mpr
  exact ⟨hR,fun w hw i => by simpa only [sortEval,iRV] using (hw.1 i).1⟩

theorem rvProductGammaBalance_append (n : ℕ) (t s : Fin n → CanonicalRV.RVSort M) :
    Fin.append (rvValues t) (rvValues s) ∈ rvProductGammaBalance (M := M) n ↔
      (∀ i, (t i).val ≠ iRVZero) ∧ (∀ i, (s i).val ≠ iRVZero) ∧
        Values.vrv (∏ i, t i) = Values.vrv (∏ i, s i) := by
  have hl : Fin.append (rvValues t) (rvValues s) ∘ Fin.castAdd n = rvValues t :=
    funext (Fin.append_left _ _)
  have hr : Fin.append (rvValues t) (rvValues s) ∘ Fin.natAdd n = rvValues s :=
    funext (Fin.append_right _ _)
  have hp : Proper (Fin.append (rvValues t) (rvValues s)) ↔
      (∀ i, (t i).val ≠ iRVZero) ∧ ∀ i, (s i).val ≠ iRVZero := by
    constructor
    · intro h
      exact ⟨fun i => by simpa only [Fin.append_left,rvValues] using (h (Fin.castAdd n i)).2,
        fun i => by simpa only [Fin.append_right,rvValues] using (h (Fin.natAdd n i)).2⟩
    · rintro ⟨ht,hs⟩ i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left,rvValues] using (show iRV (t i).val ∧ (t i).val ≠ iRVZero from ⟨(t i).property,ht i⟩)
      · simpa only [Fin.append_right,rvValues] using (show iRV (s i).val ∧ (s i).val ≠ iRVZero from ⟨(s i).property,hs i⟩)
  change (_ ∧ _ ∧ _) ↔ _
  rw [hl,hr,rvTupleProductTerm_realize,rvTupleProductTerm_realize]
  have he : Values.vrv (∏ i, t i) = Values.vrv (∏ i, s i) ↔
      iLe (∏ i, t i).val (∏ i, s i).val ∧ iLe (∏ i, s i).val (∏ i, t i).val :=
    Values.vrv_eq_iff _ _
  rw [← he,hp]
  tauto

end IntegrationInACVF.Section7
