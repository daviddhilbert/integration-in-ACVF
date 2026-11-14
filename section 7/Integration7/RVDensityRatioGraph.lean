import Integration7.RVProductGammaBalance
import Integration7.RVNonzero

/-! A parameter-free formula for the nonzero density ratio, using the
released multiplication and totalized inversion symbols. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section8

namespace IntegrationInACVF.Section7

def rvDensityRatioTerm : LRV.Term (Fin 2) :=
  .func Fn.rvMul ![.var 0,.func Fn.rvInv ![.var 1] ]

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem realizeRatioMul {ι : Type} (A B : LRV.Term ι) (z : ι → M) :
    (Term.func Fn.rvMul ![A,B]).realize z = iRVMul (A.realize z) (B.realize z) := by
  change Structure.funMap (L := LRV) Fn.rvMul (fun i => (![A,B] i).realize z) = _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem realizeRatioInv {ι : Type} (A : LRV.Term ι) (z : ι → M) :
    (Term.func Fn.rvInv ![A]).realize z = iRVInvFn (A.realize z) := by
  change Structure.funMap (L := LRV) Fn.rvInv (fun i => (![A] i).realize z) = _
  congr 1
  funext i
  fin_cases i
  rfl

theorem rvDensityRatioTerm_realize (r : Fin 2 → CanonicalRV.RVSort M) :
    rvDensityRatioTerm.realize (rvValues r) = (r 0 / r 1).val := by
  rw [rvDensityRatioTerm,realizeRatioMul,realizeRatioInv,Term.realize_var,Term.realize_var,
    div_eq_mul_inv,RVOperations.mul_val,RVOperations.inv_val]
  rfl

def rvDensityRatioGraph : Set (Fin (2+1) → M) :=
  {w | Proper w ∧ w (Fin.natAdd 2 (0 : Fin 1)) = rvDensityRatioTerm.realize (w ∘ Fin.castAdd 1)}

theorem rvDensityRatioGraph_raw_definable (S : Set M) : S.Definable LRV (rvDensityRatioGraph (M := M)) := by
  have hP : S.Definable LRV {w : Fin (2+1) → M | Proper w} := by
    convert Set.definable_iInter_of_finite (fun i : Fin (2+1) =>
      (nonzero_rv_definable S).preimage_comp (fun _ : Fin 1 => i)) using 1
    ext w
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_preimage,Proper,Function.comp_apply]
    rfl
  have hT : S.DefinableFun LRV (fun w : Fin (2+1) → M =>
      rvDensityRatioTerm.realize (w ∘ Fin.castAdd 1)) :=
    Set.DefinableFun.comp (f := fun v : Fin 2 → M => rvDensityRatioTerm.realize v)
      (g := fun w : Fin (2+1) → M => w ∘ Fin.castAdd 1)
      (show S.DefinableMap LRV (fun w : Fin (2+1) → M => w ∘ Fin.castAdd 1) from
        fun _ => Set.DefinableFun.proj LRV)
      (Set.DefinableFun.of_empty (rvDensityRatioTerm.definableFun_realize (M := M)))
  exact hP.inter ((Set.DefinableFun.proj (L := LRV) (A := S) (i := Fin.natAdd 2 (0 : Fin 1))).ofPred_eq hT)

theorem rvDensityRatioGraph_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin (2+1) => .rv) (rvDensityRatioGraph (M := M)) := by
  let R := rvDensityRatioGraph (M := M)
  have hR : @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin (2+1)) R :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M (@Base.real M sM hM B) LRV I (Fin (2+1)) R)
      (normalize_eq_of_isCanonical hc).symm) (rvDensityRatioGraph_raw_definable B.real)
  apply real_definableOverBase B _ _
  apply (definableOver_iff_normalized_raw B.real _ _).mpr
  exact ⟨hR,fun w hw i => by simpa only [sortEval,iRV] using (hw.1 i).1⟩

theorem rvDensityRatioGraph_append (r : Fin 2 → CanonicalRV.RVSort M)
    (s : Fin 1 → CanonicalRV.RVSort M) :
    Fin.append (rvValues r) (rvValues s) ∈ rvDensityRatioGraph (M := M) ↔
      Proper (Fin.append (rvValues r) (rvValues s)) ∧ s 0 = r 0 / r 1 := by
  have he : Fin.append (rvValues r) (rvValues s) ∘ Fin.castAdd 1 = rvValues r :=
    funext (Fin.append_left _ _)
  change (_ ∧ _ = _) ↔ _
  rw [Fin.append_right,he,rvDensityRatioTerm_realize]
  exact and_congr_right (fun _ => ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩)

theorem rvDensityRatioGraph_output (a b : CanonicalRV.RVSort M) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fin.append (rvValues ![a,b]) (rvValues (fun _ : Fin 1 => a / b)) ∈ rvDensityRatioGraph (M := M) := by
  apply (rvDensityRatioGraph_append _ _).mpr
  refine ⟨?_,rfl⟩
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · fin_cases i
    · change iRV a.val ∧ a.val ≠ iRVZero
      exact ⟨a.property,(rv_nonzero_iff_raw a).mp ha⟩
    · change iRV b.val ∧ b.val ≠ iRVZero
      exact ⟨b.property,(rv_nonzero_iff_raw b).mp hb⟩
  · simpa only [Fin.append_right,rvValues] using
      (show iRV (a / b).val ∧ (a / b).val ≠ iRVZero from
        ⟨(a / b).property,(rv_nonzero_iff_raw _).mp (div_ne_zero ha hb)⟩)

end IntegrationInACVF.Section7
