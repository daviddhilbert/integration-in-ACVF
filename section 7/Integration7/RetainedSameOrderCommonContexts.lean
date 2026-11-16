module

public import Integration7.RetainedDensitySameOrderContractions
public import Integration7.CommonContextVolumeEquivalences
public import Integration7.PositiveSelectedLemma75

@[expose] public section

/-! Same-order retained-density comparison as an explicit common-context
relation, over the original real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem retained_same_order_common_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T E : StandardContraction A σ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let R := fun (P : StandardContraction A σ) => retainedDensityContractionGammaObject
      C.uncountable.le C.saturated C.small hc C (Set.Subset.refl _) A
      ((gammaLogicInput G).real_set _ (setDefinable A)) hfin δ (fun p => hδ p.val p.property)
      P (gamma_program_over_real_base G P.program)
    CommonContextVolumeEquivalent G C (R T) (R E) := by
  intro G R
  exact retained_density_same_order_contractions_compare (G := G) (k := n) hc C C.uncountable.le C.saturated C.small hΞ
    γ hγ hγ1 (Set.Subset.refl _) (fun _ h => h) A
    ((gammaLogicInput G).real_set _ (setDefinable A)) hfin δ (fun p => hδ p.val p.property)
    T E (gamma_program_over_real_base G T.program) (gamma_program_over_real_base G E.program)

end IntegrationInACVF.Section7
