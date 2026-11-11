import IntegrationSection4.OneCellDecomposition
import IntegrationSection4.TwoCellDecomposition

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.ParameterizedCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def oneFibre {m : ℕ} (A : Set (Point (M := M) 1 m)) (s : Fin m → RV (M := M)) :
    Set (VF (M := M)) := {x | (fun _ => x,s) ∈ A}

def twoFibre {m : ℕ} (A : Set (Point (M := M) 2 m)) (s : Fin m → RV (M := M)) :
    Set (VF (M := M) × VF (M := M)) := {p | ((pairPoint p.1 p.2).1,s) ∈ A}

/-- The parameterized versions in Definition 4.7. Only labels in the
actual RV projection have to give cells; other slices are empty. -/
def IsOneCell {m : ℕ} (A : Set (Point (M := M) 1 m)) : Prop :=
  ∀ s, (oneFibre A s).Nonempty → Cells.IsOneCell (oneFibre A s)

def IsTwoCell {m : ℕ} (A : Set (Point (M := M) 2 m)) : Prop :=
  ∀ s, (twoFibre A s).Nonempty → Cells.IsTwoCell (twoFibre A s)

def DefinableOneCell (G : GammaParameters.Base (M := M)) {m : ℕ}
    (A : Set (Point (M := M) 1 m)) : Prop :=
  GammaSetDefinable G A ∧ ∀ s, (oneFibre A s).Nonempty →
    Cells.DefinableOneCell (RVLabelSlices.labelBase G s) (oneFibre A s)

def DefinableTwoCell (G : GammaParameters.Base (M := M)) {m : ℕ}
    (A : Set (Point (M := M) 2 m)) : Prop :=
  GammaSetDefinable G A ∧ ∀ s, (twoFibre A s).Nonempty →
    Cells.DefinableTwoCell (RVLabelSlices.labelBase G s) (twoFibre A s)

end IntegrationInACVF.Section4.ParameterizedCells
