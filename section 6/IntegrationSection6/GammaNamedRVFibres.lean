import IntegrationSection6.GammaRawRVFormulas
import Section3.GammaClosureLaws

/-! Fixing any chosen old RV labels is definable over precisely those
named RV values and the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m e : ℕ}

theorem gamma_named_rv_label_fibre (ρ : Fin e → Fin m) (t : Fin e → RV (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      {p : Point (M := M) n m | p.2 ∘ ρ = t} := by
  let Bt : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  have hSingle : DefinableOverBase Bt (fun _ : Fin e => .rv) {fun j => (t j).val} :=
    tuple_singleton_definable_base Bt _ _ (fun j => real_definableAtBase Bt .rv _
      (definableClosureAt_of_mem (Or.inr ⟨j,rfl⟩) (t j).property))
  let π : Fin e → Fin (n+m) := fun j => Fin.natAdd n (ρ j)
  have h := hSingle.preimage_real (gammaPointSort n m) π
  have hh := gamma_set_of_sorted_formula h
  convert hh using 1
  apply Set.ext
  intro p
  change p.2 ∘ ρ = t ↔ gammaPointCode p ∘ π ∈ {fun j => (t j).val} ∧ _
  have he : gammaPointCode p ∘ π = fun j => (p.2 (ρ j)).val := by
    funext j
    simp only [Function.comp_apply,π,gammaPointCode,Fin.append_right]
  rw [he,Set.mem_singleton_iff]
  constructor
  · intro ht
    exact ⟨congrArg (fun w => fun j => (w j).val) ht,gammaPointCode_proper p⟩
  · rintro ⟨ht,_⟩
    funext j
    exact Subtype.ext (congrFun ht j)

end IntegrationInACVF.Section6
