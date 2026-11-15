import IntegrationSection6.CompletedSection5Refinements
import IntegrationSection6.Section5TwoOrderInput

/-! The actual Section 5.8 theorem fills the two-order interface on each
base satisfying its standing hypotheses. The arbitrary-base universal
interface is kept separate rather than silently strengthened or assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem fin_two_permutation_cases (σ : Equiv.Perm (Fin 2)) :
    σ = Equiv.refl _ ∨ σ = Equiv.swap 0 1 := by
  have hValue (i : Fin 2) : σ i = 0 ∨ σ i = 1 := by
    omega
  have hNe : σ (1 : Fin 2) ≠ σ 0 := σ.injective.ne (by decide)
  rcases hValue 0 with h0 | h0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · change σ 1 = 1
      rcases hValue 1 with h1 | h1
      · exact False.elim (hNe (h1.trans h0.symm))
      · exact h1
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · change σ 0 = Equiv.swap (0 : Fin 2) 1 0
      rw [Equiv.swap_apply_left]
      exact h0
    · change σ 1 = Equiv.swap (0 : Fin 2) 1 1
      rw [Equiv.swap_apply_right]
      rcases hValue 1 with h1 | h1
      · exact h1
      · exact False.elim (hNe (h1.trans h0.symm))

theorem completed_section5_two_order_input {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real) :
    Section5TwoOrderInput B hκ hs hsmall := by
  intro a U hU hfinU σ υ hNe
  obtain ⟨b,V,hV,hfinV,f,hf,hF,hVF,T,E,hT,hE,⟨e⟩⟩ :=
    FiniteRV.completed_section5_two_order_refinement hκ hs h00 B hsmall hGenerated δ hδ hδ1 FBase U hU hfinU
  rcases fin_two_permutation_cases σ with rfl | rfl <;>
    rcases fin_two_permutation_cases υ with rfl | rfl
  · exact False.elim (hNe rfl)
  · exact ⟨b,V,hV,hfinV,f,hf,hF,hVF,T,E,hT,hE,⟨e⟩⟩
  · exact ⟨b,V,hV,hfinV,f,hf,hF,hVF,E,T,hE,hT,⟨FiniteRV.gammaIsoSymm e⟩⟩
  · exact False.elim (hNe rfl)

end IntegrationInACVF.Section6
