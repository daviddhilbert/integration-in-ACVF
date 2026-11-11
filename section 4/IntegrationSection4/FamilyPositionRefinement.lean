import IntegrationSection4.FamilyLocalConstancy
import IntegrationSection4.FiniteImageFamilies

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyPositionRefinement

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def RVRefinement {n d : ℕ} (B : FullBaseAtomicity.Base (M := M))
    (A : (Fin n → M) → Set M) (e : (Fin n → M) → M → Fin d → M) : Prop :=
  (∀ p x, x ∈ A p → ∀ i, iRV (e p x i)) ∧
    FullBaseAtomicity.OverBase B {z : (Fin n ⊕ Fin 1) ⊕ Fin d → M |
      z (.inl (.inr 0)) ∈ A (z ∘ Sum.inl ∘ Sum.inl) ∧
        z ∘ Sum.inr = e (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))}

/-- Uniform constant-or-injective refinement of scalar functions, with
both parts and their finite RV graphs over the original interpreted base.
The two domains are the locally constant locus and its complement in A. -/
theorem constant_or_injective {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {n : ℕ}
    (A : (Fin n → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin n → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph B A f) :
    ∃ d₀ : ℕ, ∃ e₀ : (Fin n → M) → M → Fin d₀ → M,
    ∃ d₁ : ℕ, ∃ e₁ : (Fin n → M) → M → Fin d₁ → M,
      RVRefinement B (fun p => LocalConstancySyntax.locus (A p) (f p)) e₀ ∧
      (∀ p x, x ∈ LocalConstancySyntax.locus (A p) (f p) → ∀ y,
        y ∈ LocalConstancySyntax.locus (A p) (f p) → e₀ p x = e₀ p y → f p x = f p y) ∧
      RVRefinement B (fun p => A p \ LocalConstancySyntax.locus (A p) (f p)) e₁ ∧
      (∀ p x, x ∈ A p \ LocalConstancySyntax.locus (A p) (f p) → ∀ y,
        y ∈ A p \ LocalConstancySyntax.locus (A p) (f p) →
        f p x = f p y → e₁ p x = e₁ p y → x = y) := by
  let L (p : Fin n → M) := LocalConstancySyntax.locus (A p) (f p)
  have hL := FamilyLocalConstancy.locus_definable B A f hf
  have hLA : ∀ p, L p ⊆ A p := fun p => LocalConstancySyntax.subset (A p) (f p)
  have hGraphL := FiniteScalarFamilies.restrict B A L f hf hL hLA
  have hOff := FullBaseAtomicity.OverBase.inter (FiniteScalarFamilies.domain_definable B A f hf) hL.compl
  have hGraphOff := FiniteScalarFamilies.restrict B A (fun p => A p \ L p) f hf hOff (fun _ _ h => h.1)
  have hFin := FamilyLocalConstancy.finite_rows hκ hs B hsmall h00 δ hδ A hAVF f hfVF hf
  obtain ⟨d₀,e₀,hs₀,hg₀,hc₀⟩ := FiniteImageFamilies.exists_refinement hκ hs h00 B hsmall
    L f (fun p x hx => hfVF p x (hLA p hx)) hGraphL (fun p => (hFin p).1)
  obtain ⟨d₁,e₁,hs₁,hg₁,hc₁⟩ := FiniteScalarFamilies.exists_refinement hκ hs h00 B hsmall
    (fun p => A p \ L p) (fun p x hx => hAVF p hx.1) f hGraphOff (fun p => (hFin p).2)
  exact ⟨d₀,e₀,d₁,e₁,⟨hs₀,hg₀⟩,hc₀,⟨fun p x hx i => hs₁ p x i (hAVF p hx.1),hg₁⟩,hc₁⟩

end IntegrationInACVF.Section4.FamilyPositionRefinement
