import IntegrationSection6.CoordinateExchange

/-! Lemma6.16 with the paper's explicit permutation conditions and standing
coefficient-field base. All objects are in the finite categories RV[k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6

theorem permutation_swap_first_two {n : ℕ} (σ υ : Equiv.Perm (Fin (n+2)))
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ) : υ = (swapFirstTwo n).trans σ := by
  apply Equiv.ext
  intro j
  change υ j = σ (swapFirstTwo n j)
  cases j using Fin.cases with
  | zero => rw [swapFirstTwo_zero]; exact h0
  | succ j =>
    cases j using Fin.cases with
    | zero => rw [swapFirstTwo_one]; exact h1
    | succ j => rw [swapFirstTwo_tail]; exact hTail j

namespace FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

theorem lemma_6_16 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hBS : B.real ⊆ S)
    (h58 : ∀ x : Fin n → VF (M := M),
      Section5TwoOrderInput ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ hκ hs
        (small_union_range hκ B.real hreal (fun j => (x j).val)))
    (U : DefSet (M := M) S (n+2) a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin (n+2))}
    (h0 : υ 0 = σ (0 : Fin (n+1)).succ) (h1 : υ (0 : Fin (n+1)).succ = σ 0)
    (hTail : ∀ j : Fin n, υ j.succ.succ = σ j.succ.succ)
    (T : StandardContraction U σ) (E : StandardContraction U υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal (gammaFiniteContraction hκ hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ hs hreal hBS hU hfinU E hE) := by
  have hOrder := permutation_swap_first_two σ υ h0 h1 hTail
  subst υ
  exact lemma_6_16_uncountable (aleph0_lt_of_small_vf_field_base h00 FBase hreal) hs h00
    hreal hgamma δ hδ hδ1 hBS h58 U hU hfinU T E hT hE

end FiniteRV
end IntegrationInACVF.Section6
