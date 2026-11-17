module

public import Integration7.NativePairPresentations
public import IntegrationSection4.ParameterizedCells

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every nonempty RV-labelled fibre of an actual definable two-cell
family has a genuine native VF² presentation over that label base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S R : Set M} {m : ℕ}

theorem definable_two_cell_pair_codes {Q : Set (VF (M := M) × VF (M := M))}
    (hQ : Cells.DefinableTwoCell G Q) : DefinableOverBase G (fun _ : Fin 2 => .vf) (Cells.pairCodes Q) := by
  obtain ⟨f,t,hCell,hPair,hf,ht,hPar⟩ := hQ
  exact hPair

def nativeTwoCellFibrePresentation (A : DefSet (M := M) S 2 m)
    (hA : ParameterizedCells.DefinableTwoCell G (carrier A))
    (u : Fin m → RV (M := M)) (hu : (ParameterizedCells.twoFibre (carrier A) u).Nonempty)
    (hNames : commonRealNames (RVLabelSlices.labelBase G u) ⊆ R) : DefSet (M := M) R 2 0 :=
  nativePairPresentation (ParameterizedCells.twoFibre (carrier A) u)
    (definable_two_cell_pair_codes (hA.2 u hu)) hNames

theorem native_two_cell_fibre_presentation_domain (A : DefSet (M := M) S 2 m)
    (hA : ParameterizedCells.DefinableTwoCell G (carrier A))
    (u : Fin m → RV (M := M)) (hu : (ParameterizedCells.twoFibre (carrier A) u).Nonempty)
    (hNames : commonRealNames (RVLabelSlices.labelBase G u) ⊆ R) :
    nativeVFPairDomain (nativeTwoCellFibrePresentation A hA u hu hNames) =
      ParameterizedCells.twoFibre (carrier A) u :=
  native_pair_presentation_domain _ _ hNames

theorem gamma_native_two_cell_fibre_presentation (A : DefSet (M := M) S 2 m)
    (hA : ParameterizedCells.DefinableTwoCell G (carrier A))
    (u : Fin m → RV (M := M)) (hu : (ParameterizedCells.twoFibre (carrier A) u).Nonempty)
    (hNames : commonRealNames (RVLabelSlices.labelBase G u) ⊆ R) :
    GammaSetDefinable (RVLabelSlices.labelBase G u)
      (carrier (nativeTwoCellFibrePresentation A hA u hu hNames)) := gamma_native_pair_presentation _ _ hNames

theorem native_two_cell_fibre_presentation_is_cell (A : DefSet (M := M) S 2 m)
    (hA : ParameterizedCells.DefinableTwoCell G (carrier A))
    (u : Fin m → RV (M := M)) (hu : (ParameterizedCells.twoFibre (carrier A) u).Nonempty)
    (hNames : commonRealNames (RVLabelSlices.labelBase G u) ⊆ R) :
    Cells.DefinableTwoCell (RVLabelSlices.labelBase G u)
      (nativeVFPairDomain (nativeTwoCellFibrePresentation A hA u hu hNames)) := by
  rw [native_two_cell_fibre_presentation_domain]
  exact hA.2 u hu

end IntegrationInACVF.Section7
