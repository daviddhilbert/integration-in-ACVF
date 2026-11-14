import Integration7.VolumeForms
import Section4.RVCoordinates

set_option backward.isDefEq.respectTransparency false

/-! Definable multiplication of two RV-valued scalar maps, using the
released RV multiplication symbol and its proved semantic operation. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvMultiply (S : Set M) :
    Map (DefSet.univ ((rawRVSpace (M := M) 1).prod (rawRVSpace 1)) S)
      (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := (rawRVSpace (M := M) 1).prod (rawRVSpace 1)
  let f (p : P.Carrier) : Fin 1 → CanonicalRV.RVSort M := fun _ => p.1 0 * p.2 0
  let F (z : Fin 1 ⊕ Fin 1 → M) : Fin 1 → M :=
    fun _ => iRVMul (z (Sum.inl 0)) (z (Sum.inr 0))
  have hF : S.DefinableMap LRV F := by
    intro i
    exact (Set.DefinableFun.of_empty
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
        (show S.DefinableMap LRV
          (fun z : Fin 1 ⊕ Fin 1 → M => ![z (Sum.inl 0), z (Sum.inr 0)]) from
          fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
  have hcode (c : P.domain) : rvValues (f (P.decode c)) = F c.val := by
    funext i
    change (((rawRVSpace (M := M) 1).decode ⟨c.val ∘ Sum.inl, c.property.1⟩ 0) *
      ((rawRVSpace (M := M) 1).decode ⟨c.val ∘ Sum.inr, c.property.2⟩ 0)).val = _
    rw [RVOperations.mul_val]
    exact congrArg₂ (fun x y : M => iRVMul x y)
      (congrFun (rvValues_decode ⟨c.val ∘ Sum.inl, c.property.1⟩) 0)
      (congrFun (rvValues_decode ⟨c.val ∘ Sum.inr, c.property.2⟩) 0)
  refine Map.ofCodes _ f F hF (fun c => ⟨f (P.decode c), hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

@[simp] theorem rvMultiply_value (S : Set M)
    (p : DefSet.univ ((rawRVSpace (M := M) 1).prod (rawRVSpace 1)) S) :
    (rvMultiply S p).val 0 = p.val.1 0 * p.val.2 0 := rfl

end IntegrationInACVF.Section7
