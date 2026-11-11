import IntegrationSection3ACVF.GammaExtremumSyntax
import IntegrationSection3ACVF.FullGammaUniformFiniteness

/-! Strict local extrema of actual definable Gamma functions are finite,
including in non-Archimedean value groups. Genuine saturation supplies
uniform bounds on finite sets of separated extrema. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaLocalExtrema

open FullGammaSyntax OrderedLocalExtrema GammaExtremumSyntax

variable {M β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [LinearOrder β]

theorem localMin_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hD : Scalar B D)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1))) :
    (OrderedLocalExtrema.localMin D f).Finite := by
  have hRadius := radius_definable B D f hD hCmp
  have hFinite (δ : Values.Gamma (M := M)) : (radiusRow D f δ).Finite :=
    radiusRow_finite D f δ (FullGammaControllers.finite_controller h00
      (B.adjoin (Sum.inr δ)) _ (radius_scalar B D f hRadius δ))
  let P : (Fin 1 ⊕ Fin 1 → Values.Gamma (M := M)) → Prop :=
    fun a => a (.inr 0) ∈ radiusRow D f (a (.inl 0))
  have hP : Definable B P := hRadius.reindex (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hRow (a : Fin 1 → Values.Gamma (M := M)) : FullGammaCounting.row P a = radiusRow D f (a 0) := rfl
  obtain ⟨N,hN⟩ := FullGammaUniformFiniteness.exists_bound hκ hs B hsmall P hP
    (fun a => hRow a ▸ hFinite (a 0))
  have hBound (δ : Values.Gamma (M := M)) :
      (radiusRow D f δ).Finite ∧ (radiusRow D f δ).ncard ≤ N := by
    refine ⟨hFinite δ,?_⟩
    exact hN ![δ]
  exact OrderedLocalExtrema.localMin_finite D f N hBound
    (FullGammaControllers.finite_controller h00 B _ (localMin_definable B D f hRadius))

theorem finite_strict_extrema {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph D f)) :
    (OrderedLocalExtrema.localMin D f).Finite ∧
      (OrderedLocalExtrema.localMin (β := OrderDual (Values.Gamma (M := M))) D f).Finite := by
  have hD := GammaFunctionSyntax.domain_definable B D f hG
  have hCmp := GammaFunctionSyntax.comparison_definable B D f hG (0 : Fin 2) 1
  have hCmpDual : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 1) < f (a 0)) := by
    apply (hCmp.reindex (![1,0] : Fin 2 → Fin 2)).congr
    intro a
    change (a 1 ∈ D ∧ a 0 ∈ D ∧ f (a 1) < f (a 0)) ↔
      (a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 1) < f (a 0))
    tauto
  exact ⟨localMin_finite hκ hs h00 B hsmall D f hD hCmp,
    localMin_finite (β := OrderDual (Values.Gamma (M := M))) hκ hs h00 B hsmall D f hD hCmpDual⟩

end IntegrationInACVF.Section3ACVF.GammaLocalExtrema
