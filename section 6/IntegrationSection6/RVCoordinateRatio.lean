import IntegrationSection6.ElementaryKeys

/-! Variable-coordinate division in the corrected named-inversion language.
This extends the coordinate-code construction of pinned RVNamedDivision
from a named denominator to an RV input coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {d : ℕ}

def rvCoordinateRatioMap (S : Set M) (p q : Fin d) :
    Map (DefSet.univ (rawRVSpace (M := M) d) S) (DefSet.univ (rawRVSpace 1) S) := by
  let F (z : Fin d → M) : Fin 1 → M := fun _ => iRVMul (z p) (iRVInvFn (z q))
  have hi : S.DefinableFun LRV (fun z : Fin d → M => iRVInvFn (z q)) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvInv)).comp
      (show S.DefinableMap LRV (fun z : Fin d → M => ![z q]) from by
        intro j; fin_cases j; exact Set.DefinableFun.proj LRV)
  have hm : S.DefinableFun LRV (fun z : Fin d → M => iRVMul (z p) (iRVInvFn (z q))) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun z : Fin d → M => ![z p,iRVInvFn (z q)]) from by
        intro j; fin_cases j; exact Set.DefinableFun.proj LRV; exact hi)
  have hF : S.DefinableMap LRV F := fun _ => hm
  have hcode (c : (rawRVSpace (M := M) d).domain) :
      rvValues (fun _ : Fin 1 => ((rawRVSpace d).decode c p) / ((rawRVSpace d).decode c q)) = F c.val := by
    funext i
    change (((rawRVSpace d).decode c p) / ((rawRVSpace d).decode c q)).val = _
    rw [div_eq_mul_inv,RVOperations.mul_val,RVOperations.inv_val]
    exact congrArg₂ iRVMul (congrFun (rvValues_decode c) p)
      (congrArg iRVInvFn (congrFun (rvValues_decode c) q))
  refine Map.ofCodes _ (fun t => fun _ : Fin 1 => t p / t q) F hF
    (fun c => ⟨_,hcode c⟩) ?_
  intro c
  exact rvValues_injective ((rvValues_decode _).trans (hcode c).symm)

@[simp] theorem rvCoordinateRatioMap_value (S : Set M) (p q : Fin d)
    (a : DefSet.univ (rawRVSpace (M := M) d) S) :
    (rvCoordinateRatioMap S p q a).val = fun _ : Fin 1 => a.val p / a.val q := rfl

end IntegrationInACVF.Section6
