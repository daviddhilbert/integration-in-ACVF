import IntegrationSection6.VFParameterCoefficientBases
import IntegrationSection5.NaturalContractionGamma

/-! The paper's standing VF/Gamma generation supplies the actual VF
field base needed by the checked all-order contraction producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

def generatedBaseVFField (hB : VFGammaGeneratedBase B) : VFFieldBase B.real :=
  hB.closure_eq_self ▸ closureBase_field B

theorem generated_base_standard_contraction_exists {κ : Cardinal}
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hGenerated : VFGammaGeneratedBase B) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ T : StandardContraction A σ, GammaProgramDefinable B T.program ∧
      GammaSetDefinable B (carrier T.target) ∧ GammaGraphDefinable B (pointMapGraph T.toMap) ∧
      GammaGraphDefinable B (pointMapGraph T.naturalMap) :=
  standard_contraction_exists_with_natural_graph hs h00 B hsmall (generatedBaseVFField hGenerated) hBS A hA σ

end IntegrationInACVF.Section7
