import IntegrationSection3ACVF.AtomicFunctionFibres
import IntegrationSection3ACVF.AtomicFibreMeanGraph
import IntegrationSection3ACVF.FiniteFibreInjectivity

/-! Constant-or-injective maps on atomic open balls, using the actual
finite-fibre means and their unchanged-base defining graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AtomicFunctionInjectivity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem constant_or_injective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A D : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (hsub : A ⊆ D) (f : M → M)
    (hf : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    (∃ c : M, ∀ x ∈ A, f x = c) ∨ Set.InjOn f A := by
  rcases AtomicFunctionFibres.constant_or_finite_fibres hκ hs B hsmall h00 δ hδ hδ1
      ho hA hsub f hf hfVF with hc | hFinite
  · exact Or.inl hc
  · have hAVF : A ⊆ {x | iVF x} := by
      rcases ho with he | ⟨a,α,he⟩
      · exact he ▸ Set.Subset.rfl
      · rw [he]
        exact fun _ hx => hx.1
    have hReal : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D f) :=
      FullBaseAtomicity.OverBase.of_real hf
    have hm := FullBaseAtomicity.OverBase.preimage_comp hA.1 (fun _ : Fin 1 => (0 : Fin 2))
    have hGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f) := by
      apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hm hReal)
      intro z
      change (z 0 ∈ A ∧ z 0 ∈ D ∧ z 1 = f (z 0)) ↔ (z 0 ∈ A ∧ z 1 = f (z 0))
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
    obtain ⟨F,hF,hMean⟩ := AtomicFibreMeanGraph.exists_mean_graph B h00 hA hAVF f hGraph hFinite
    exact Or.inr (FiniteFibreInjectivity.injOn_of_definable_fibre_mean B h00 δ hδ hδ1 ho hA f F hF hMean)

end IntegrationInACVF.Section3ACVF.AtomicFunctionInjectivity
