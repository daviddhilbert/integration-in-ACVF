import Section9.RVScaleRatio

/-! A parameter-free term for the actual RV tuple product, including the
empty product. This supplies a finite formula for Gamma weight balance. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

def rvTupleProductTerm : (n : ℕ) → LRV.Term (Fin n)
  | 0 => .func Fn.rvOne Fin.elim0
  | n+1 => .func Fn.rvMul ![Term.relabel Fin.castSucc (rvTupleProductTerm n),.var (Fin.last n)]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private theorem realizeRVTupleProductMul {ι : Type} (A B : LRV.Term ι) (z : ι → M) :
    (Term.func Fn.rvMul ![A,B]).realize z = iRVMul (A.realize z) (B.realize z) := by
  change Structure.funMap (L := LRV) Fn.rvMul (fun i => (![A,B] i).realize z) = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem rvTupleProductTerm_realize (n : ℕ) (t : Fin n → CanonicalRV.RVSort M) :
    (rvTupleProductTerm n).realize (rvValues t) = (∏ i, t i).val := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero,RVOperations.one_val]
    change Structure.funMap (L := LRV) Fn.rvOne (fun i => (Fin.elim0 i : LRV.Term (Fin 0)).realize _) = _
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    rw [rvTupleProductTerm,realizeRVTupleProductMul,Term.realize_relabel,Term.realize_var]
    change iRVMul ((rvTupleProductTerm n).realize (rvValues (t ∘ Fin.castSucc)))
      ((t (Fin.last n)).val) = _
    rw [ih,Fin.prod_univ_castSucc,RVOperations.mul_val]
    rfl

end IntegrationInACVF.Section7
