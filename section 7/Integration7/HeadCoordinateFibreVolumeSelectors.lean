module

public import Integration7.HeadCoordinateFibreContraction
public import IntegrationSection6.GammaHeadSelectedFiniteness

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The restricted unary program keeps the same head RV tag and the
same suffix of old labels as the original head preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {U : DefSet (M := M) S (n+1) a}

theorem head_coordinate_fibre_volume_index (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    (headCoordinateFibreContraction T x).volumeIndex 0 = Fin.castAdd T.arity (0 : Fin 1) := by
  change (orderedCastSource (.step (headCoordinateFibrePreparation T x) (.zero _))
    (vfPermutationImage_id_eq _).symm).volumeIndex 0 = _
  rw [orderedCastSource_volumeIndex]
  apply Fin.ext
  simp [OrderedContractionProgram.volumeIndex,suffixIndex]

theorem head_coordinate_fibre_old_label_index (T : HeadPreparation U)
    (x : Fin n → VF (M := M)) (δ : Fin a) :
    suffixIndex (headCoordinateFibreContraction T x).program.rvArity_le δ =
      Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ) := by
  apply Fin.ext
  change 1+T.arity-a+δ.val = 1+(T.arity-a+δ.val)
  have h := specialRelative_rvArity_le T.special
  omega

end IntegrationInACVF.Section7
