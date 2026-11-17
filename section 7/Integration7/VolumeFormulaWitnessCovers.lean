module

public import Integration7.GammaVolumeChainSchemata
public import IntegrationSection6.GammaWitnessUniformity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A pointwise cover by valid common-witness formulas has a finite
subcover with uniformly bounded chain lengths, with arbitrary auxiliary
exception certificates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem volume_formula_common_finite_cover {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (A : Set (Fin p → M)) (hA : DefinableOverBase B sp A)
    (hWitness : ∀ z ∈ A, ∃ H : GammaVolumeCommonSchema F G, H.valid z) :
    ∃ J : Finset (GammaVolumeCommonSchema F G), ∃ bound : ℕ,
      ∀ z ∈ A, ∃ H ∈ J, H.leftLength ≤ bound ∧ H.rightLength ≤ bound ∧ H.valid z := by
  obtain ⟨J,N,hJ⟩ := Section6.gamma_uniform_witness_length hκ hs hreal hgamma sp A hA
    (fun H : GammaVolumeCommonSchema F G => {z | H.valid z}) (fun H => H.valid_definable hc)
    (fun H => max H.leftLength H.rightLength) hWitness
  refine ⟨J,N,?_⟩
  intro z hz
  obtain ⟨H,hH,hN,hV⟩ := hJ z hz
  exact ⟨H,hH,(le_max_left _ _).trans hN,(le_max_right _ _).trans hN,hV⟩

end IntegrationInACVF.Section7
