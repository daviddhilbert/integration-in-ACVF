import Integration7.ScalarRVMaps
import Section3.DefinableConstants

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rvScalarOne {P : Space LRV M} (A : DefSet P S) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  have hc : S.DefinableFun LRV (fun _ : P.Index → M => iRVOne) :=
    (SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol (L := LRV)
        Fn.rvOne Fin.elim0 (fun i => i.elim0))).mono (Set.empty_subset S)
  refine Map.ofCodes A (fun _ => fun _ => 1) (fun _ => fun _ => iRVOne)
    (fun _ => hc) (fun _ => ⟨fun _ => (1 : CanonicalRV.RVSort M), ?_⟩) ?_
  · funext i
    exact RVOperations.one_val
  · intro c
    apply rvValues_injective
    exact (rvValues_decode _).trans (funext (fun _ => RVOperations.one_val.symm))

@[simp] theorem rvScalarOne_value {P : Space LRV M} (A : DefSet P S) (a : A) :
    (rvScalarOne A a).val 0 = 1 := rfl

def rvInverse (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S)
      (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let F (z : Fin 1 → M) : Fin 1 → M := fun _ => iRVInvFn (z 0)
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvInv)).comp
      (show S.DefinableMap LRV (fun z : Fin 1 → M => ![z 0]) from
        fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  let f (t : Fin 1 → CanonicalRV.RVSort M) : Fin 1 → CanonicalRV.RVSort M :=
    fun _ => (t 0)⁻¹
  have hcode (c : (rawRVSpace (M := M) 1).domain) :
      rvValues (f ((rawRVSpace 1).decode c)) = F c.val := by
    funext i
    change (((rawRVSpace (M := M) 1).decode c 0)⁻¹).val = _
    rw [RVOperations.inv_val]
    exact congrArg iRVInvFn (congrFun (rvValues_decode c) 0)
  refine Map.ofCodes _ f F hF (fun c => ⟨_, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

@[simp] theorem rvInverse_value (S : Set M)
    (t : DefSet.univ (rawRVSpace (M := M) 1) S) :
    (rvInverse S t).val 0 = (t.val 0)⁻¹ := rfl

def rvScalarMul {P : Space LRV M} {A : DefSet P S}
    (f g : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  (rvMultiply S).comp (f.pair g).toUniv

@[simp] theorem rvScalarMul_value {P : Space LRV M} {A : DefSet P S}
    (f g : Map A (DefSet.univ (rawRVSpace (M := M) 1) S)) (a : A) :
    (rvScalarMul f g a).val 0 = (f a).val 0 * (g a).val 0 := rfl

end IntegrationInACVF.Section7
