import IntegrationSection3ACVF.GammaFunctionSyntax
import IntegrationSection3ACVF.OrderedLocalExtrema

/-! Definability of strict local extrema on the actual Gamma input.
The ordered output is arbitrary; reversing it also covers local maxima. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaExtremumSyntax

open FullGammaSyntax OrderedLocalExtrema

variable {M β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [LinearOrder β]

def radiusRelation (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (a : Fin 2 → Values.Gamma (M := M)) : Prop := a 1 ∈ radiusRow D f (a 0)

theorem radius_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hD : Scalar B D)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1))) :
    Definable B (radiusRelation D f) := by
  let ι := Fin 2 ⊕ Fin 1
  let δ : ι := .inl 0
  let x : ι := .inl 1
  let y : ι := .inr 0
  have hCmp' := hCmp.reindex (![x,y] : Fin 2 → ι)
  have hPrem := (((unary_at hD y).and (GammaFunctionSyntax.lt_mul_definable B y x δ)).and
    (GammaFunctionSyntax.lt_mul_definable B x y δ)).and (eq_definable B y x).not
  have hd := ((GammaFunctionSyntax.one_lt_definable B (0 : Fin 2)).and
    (unary_at hD (1 : Fin 2))).and (hPrem.imp hCmp').forall_block
  apply hd.congr
  intro a
  change ((1 < a 0 ∧ a 1 ∈ D) ∧ ∀ b : Fin 1 → Values.Gamma (M := M),
    (((b 0 ∈ D ∧ b 0 < a 1 * a 0) ∧ a 1 < b 0 * a 0) ∧ b 0 ≠ a 1) →
      a 1 ∈ D ∧ b 0 ∈ D ∧ f (a 1) < f (b 0)) ↔
    (1 < a 0 ∧ a 1 ∈ D ∧ ∀ y ∈ D, y < a 1*a 0 → a 1 < y*a 0 → y ≠ a 1 → f (a 1) < f y)
  constructor
  · rintro ⟨⟨hδ,hx⟩,h⟩
    exact ⟨hδ,hx,fun y hy h1 h2 hne => (h ![y] ⟨⟨⟨hy,h1⟩,h2⟩,hne⟩).2.2⟩
  · rintro ⟨hδ,hx,h⟩
    exact ⟨⟨hδ,hx⟩,fun b ⟨⟨⟨hy,h1⟩,h2⟩,hne⟩ => ⟨hx,hy,h (b 0) hy h1 h2 hne⟩⟩

theorem radius_scalar (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hRadius : Definable B (radiusRelation D f)) (δ : Values.Gamma (M := M)) :
    Scalar (B.adjoin (Sum.inr δ)) (radiusRow D f δ) := by
  let C := B.adjoin (Sum.inr δ)
  have hRC : Definable C (radiusRelation D f) :=
    FullBaseAtomicity.OverBase.mono hRadius Set.Subset.rfl (Set.subset_insert _ _)
  have hδ : Scalar C {δ} := AdjoinGamma.named_scalar δ (Set.mem_insert _ _)
  have hd := FullGammaControllers.fix_last C (hRC.reindex (![1,0] : Fin 2 → Fin 2)) δ hδ
  apply (scalar_definable_iff (radiusRow D f δ)).mp
  exact hd

theorem localMin_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hRadius : Definable B (radiusRelation D f)) : Scalar B (localMin D f) := by
  have hd := (hRadius.reindex (![.inr 0,.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1)).exists_block
  apply (scalar_definable_iff (localMin D f)).mp
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), a 0 ∈ radiusRow D f (b 0)) ↔ a 0 ∈ localMin D f
  rw [localMin_iff_radius]
  exact ⟨fun ⟨b,hb⟩ => ⟨b 0,hb⟩,fun ⟨δ,hδ⟩ => ⟨![δ],hδ⟩⟩

end IntegrationInACVF.Section3ACVF.GammaExtremumSyntax
