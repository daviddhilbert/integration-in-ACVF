module

public import Integration7.ScalarRVAlgebra
public import Section4.VFRealFibres

@[expose] public section

/-! Definable scalar reduction and replacement of the absorbing RV
value by1. Nonzero scalar values are retained literally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def scalarEncodedRVMap (S : Set M) :
    Map (DefSet.univ (rawVFSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawVFSpace (M := M) 1
  let Q := rawRVSpace (M := M) 1
  let R (a : P.Carrier) : Q.Carrier := fun i => CanonicalRV.encodedRv (a i)
  let F (z : P.Index → M) : Q.Index → M := fun i => iRv (z i)
  have hF (z : P.domain) : rvValues (R (P.decode z)) = F z.val := by
    funext i
    exact congrArg iRv (congrFun (vfValues_decode z) i)
  have hdom (z : P.domain) : F z.val ∈ Q.domain := ⟨R (P.decode z),hF z⟩
  refine Map.ofCodes _ R F (fun i => ?_) hdom (fun z => ?_)
  · exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![z i]) from
        fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  · exact rvValues_injective ((rvValues_decode ⟨F z.val,hdom z⟩).trans (hF z).symm)

theorem scalar_encoded_rv_map_value (S : Set M) (p : DefSet.univ (rawVFSpace (M := M) 1) S) :
    (scalarEncodedRVMap S p).val 0 = CanonicalRV.encodedRv (p.val 0) := rfl

def nonzeroRVScalarMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawRVSpace (M := M) 1
  let R (t : P.Carrier) : P.Carrier := fun _ => if (t 0).val = iRVZero then 1 else t 0
  let F (z : Fin 1 → M) : Fin 1 → M := fun _ => if z 0 = iRVZero then iRVOne else z 0
  have hz : S.DefinableFun LRV (fun _ : Fin 1 → M => iRVZero) :=
    (SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol (L := LRV)
      Fn.rvZero Fin.elim0 (fun i => i.elim0))).mono (Set.empty_subset S)
  have ho : S.DefinableFun LRV (fun _ : Fin 1 → M => iRVOne) :=
    (SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol (L := LRV)
      Fn.rvOne Fin.elim0 (fun i => i.elim0))).mono (Set.empty_subset S)
  have hproj : S.DefinableFun LRV (fun z : Fin 1 → M => z 0) := Set.DefinableFun.proj LRV
  have hF : S.DefinableMap LRV F := fun _ => Set.DefinableFun.ite (hproj.ofPred_eq hz) ho hproj
  have hcode (z : P.domain) : rvValues (R (P.decode z)) = F z.val := by
    funext i
    change (if ((P.decode z) 0).val = iRVZero then (1 : CanonicalRV.RVSort M) else (P.decode z) 0).val = _
    have he := congrFun (rvValues_decode z) 0
    change ((P.decode z) 0).val = z.val (0 : Fin 1) at he
    change _ = (if z.val (0 : Fin 1) = iRVZero then iRVOne else z.val (0 : Fin 1))
    simp only [apply_ite,RVOperations.one_val,he]
    split_ifs <;> simp_all
  have hdom (z : P.domain) : F z.val ∈ P.domain := ⟨R (P.decode z),hcode z⟩
  exact Map.ofCodes _ R F hF hdom
    (fun z => rvValues_injective ((rvValues_decode ⟨F z.val,hdom z⟩).trans (hcode z).symm))

theorem nonzero_rv_scalar_map_nonzero (S : Set M) (p : DefSet.univ (rawRVSpace (M := M) 1) S) :
    (nonzeroRVScalarMap S p).val 0 ≠ 0 := by
  change (if (p.val 0).val = iRVZero then 1 else p.val 0) ≠ 0
  split_ifs with h
  · exact one_ne_zero
  · exact fun he => h ((congrArg Subtype.val he).trans RVOperations.zero_val)

theorem nonzero_rv_scalar_map_of_nonzero (S : Set M)
    (p : DefSet.univ (rawRVSpace (M := M) 1) S) (hp : p.val 0 ≠ 0) :
    (nonzeroRVScalarMap S p).val 0 = p.val 0 := by
  change (if (p.val 0).val = iRVZero then 1 else p.val 0) = p.val 0
  rw [if_neg]
  exact fun he => hp (Subtype.ext (he.trans RVOperations.zero_val.symm))

end IntegrationInACVF.Section7
