import IntegrationSection3ACVF.GammaLocalExtrema
import IntegrationSection3ACVF.GammaGermSyntax
import IntegrationSection3ACVF.OrderedFunctionGerms
import IntegrationSection3ACVF.FiniteOrderIntervalPatterns
import Mathlib.Order.Interval.Set.OrdConnected

/-! A finite cut set makes an actual definable injective Gamma function
strictly monotone on each open interval in its domain that avoids the cuts.
All local-sign, finite-extremum and prefix-controller inputs are proved. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.GammaPiecewiseMonotonicity

open FullGammaSyntax GammaGermSyntax OrderedGermMonotonicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_cuts {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph D f)) (hInj : Set.InjOn f D) :
    ∃ F : Finset (Values.Gamma (M := M)), ∀ l u, l < u →
      (∀ x ∈ Set.Ioo l u, x ∉ F) → Set.Ioo l u ⊆ D →
      StrictMonoOn f (Set.Ioo l u) ∨ StrictAntiOn f (Set.Ioo l u) := by
  classical
  have hD := GammaFunctionSyntax.domain_definable B D f hG
  have hCmp := GammaFunctionSyntax.comparison_definable B D f hG (0 : Fin 2) 1
  have hCmpDual : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 1) < f (a 0)) := by
    apply (hCmp.reindex (![1,0] : Fin 2 → Fin 2)).congr
    intro a
    change (a 1 ∈ D ∧ a 0 ∈ D ∧ f (a 1) < f (a 0)) ↔ _
    tauto
  obtain ⟨F,hF⟩ := FullGammaControllers.finite_controller h00 B _ (increasing_definable B D f hD hCmp)
  obtain ⟨hMin,hMax⟩ := GammaLocalExtrema.finite_strict_extrema hκ hs h00 B hsmall D f hG
  let H := F ∪ hMin.toFinset ∪ hMax.toFinset
  refine ⟨H,?_⟩
  intro l u hlu hAvoid hID
  have hAvoidF (x : Values.Gamma (M := M)) (hx : x ∈ Set.Ioo l u) : x ∉ F := by
    intro hxF
    exact hAvoid x hx (Finset.mem_union_left _ (Finset.mem_union_left _ hxF))
  have hClass (x : Values.Gamma (M := M)) (hx : x ∈ Set.Ioo l u) :
      increasing D f x ∨ increasing (β := OrderDual (Values.Gamma (M := M))) D f x := by
    have hc := OrderedFunctionGerms.classify D f hInj x (hID hx) ⟨l,u,hx.1,hx.2,hID⟩
      (comparison_controller h00 B D f hCmp x (hID hx))
    rcases hc with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hAvoid x hx (Finset.mem_union_left _ (Finset.mem_union_right _ (hMin.mem_toFinset.mpr h)))).elim
    · exact (hAvoid x hx (Finset.mem_union_right _ (hMax.mem_toFinset.mpr h))).elim
  obtain ⟨p,hlp,hpu⟩ := exists_between hlu
  have hp : p ∈ Set.Ioo l u := ⟨hlp,hpu⟩
  have hSame (x : Values.Gamma (M := M)) (hx : x ∈ Set.Ioo l u) :
      x ∈ increasingSet D f ↔ p ∈ increasingSet D f :=
    hF x p (FiniteOrderIntervalPatterns.same_pattern F l u hAvoidF hx hp)
  by_cases hpInc : p ∈ increasingSet D f
  · refine Or.inl (strictMonoOn_of_local (Set.Ioo l u) f Set.ordConnected_Ioo ?_ ?_)
    · intro x hx
      obtain ⟨⟨a,hax,hL⟩,b,hxb,hR⟩ := ((hSame x hx).mpr hpInc).2
      exact ⟨⟨a,hax,fun y hy => hL y (hID hy)⟩,⟨b,hxb,fun y hy => hR y (hID hy)⟩⟩
    · intro a ha b hb hab
      exact prefix_controller h00 B D f hCmp a b (hID ha) (fun x hx => hID (Set.ordConnected_Ioo.out ha hb hx))
  · refine Or.inr (strictMonoOn_of_local (β := OrderDual (Values.Gamma (M := M)))
      (Set.Ioo l u) f Set.ordConnected_Ioo ?_ ?_)
    · intro x hx
      have hNot : ¬ increasing D f x := fun h => hpInc ((hSame x hx).mp ⟨hID hx,h⟩)
      obtain ⟨⟨a,hax,hL⟩,b,hxb,hR⟩ := (hClass x hx).resolve_left hNot
      exact ⟨⟨a,hax,fun y hy => hL y (hID hy)⟩,⟨b,hxb,fun y hy => hR y (hID hy)⟩⟩
    · intro a ha b hb hab
      exact prefix_controller (β := OrderDual (Values.Gamma (M := M))) h00 B D f hCmpDual
        a b (hID ha) (fun x hx => hID (Set.ordConnected_Ioo.out ha hb hx))

end IntegrationInACVF.Section3ACVF.GammaPiecewiseMonotonicity
