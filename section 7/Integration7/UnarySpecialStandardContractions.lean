module

public import Integration7.UnarySpecialHeadPreparations
public import Integration7.AppendedHeadIntegralPrograms

@[expose] public section

/-! A genuine unary special preparation supplies an identity-order
standard contraction with exactly its head coordinates and old density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b k : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))

def unarySpecialStandardContraction : StandardContraction A (Equiv.refl _) :=
  standardFromProgram A (Equiv.refl _) (unarySpecialContractionProgram T hB) (vfPermutationImage_id_eq A).symm

theorem unary_special_standard_append_index (ρ : Fin (k+1) → Fin a) :
    orderedAppendVolumeIndex (unarySpecialStandardContraction T hB).program ρ =
      headAppendVolumeIndex (unarySpecialHeadPreparation T hB) ρ := by
  change orderedAppendVolumeIndex (orderedCastSource (unarySpecialContractionProgram T hB) _) ρ = _
  rw [ordered_cast_source_appended_index]
  rfl

theorem unary_special_standard_density_index (δ : Fin a) :
    orderedAppendDensityIndex (unarySpecialStandardContraction T hB).program δ =
      Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ) := by
  change orderedAppendDensityIndex (orderedCastSource (unarySpecialContractionProgram T hB) _) δ = _
  rw [ordered_cast_source_density_index]
  rfl

theorem unary_special_standard_gamma {P : Base (M := M)} (hT : GammaChainDefinable P T.chain) :
    GammaProgramDefinable P (unarySpecialStandardContraction T hB).program :=
  gamma_standardFromProgram A (Equiv.refl _) (unarySpecialContractionProgram T hB) _
    (gamma_unary_special_contraction_program T hB hT)
end IntegrationInACVF.Section7
