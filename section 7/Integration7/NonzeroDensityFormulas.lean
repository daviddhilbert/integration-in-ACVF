import Integration7.EssentialFiniteVolumeSchemata

/-! Impose nonvanishing on a density formula at every parameter row,
without changing a specified row that already has nonzero density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}

def nonzeroDensityFormula (H : Set (Fin ((p+a)+1) → M)) : Set (Fin ((p+a)+1) → M) :=
  {w | w ∈ H ∧ w (Fin.last (p+a)) ≠ iRVZero}

theorem nonzeroDensityFormula_definable {H : Set (Fin ((p+a)+1) → M)}
    (hH : DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) H) :
    DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv))
      (nonzeroDensityFormula H) := by
  let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin 1 => .rv)
  have h := hH.inter ((nonzeroRVTuples_definable B 1).preimage_real st (fun _ => Fin.last (p+a)))
  convert h using 1
  ext w
  change (_ ∧ _) ↔ (_ ∧ (Proper _ ∧ _))
  constructor
  · rintro ⟨hw,hn⟩
    refine ⟨hw,⟨?_,hH.proper w hw⟩⟩
    intro i
    refine ⟨?_,hn⟩
    change iRV (w (Fin.natAdd (p+a) (0 : Fin 1)))
    have hs := hH.proper w hw (Fin.natAdd (p+a) (0 : Fin 1))
    simpa only [Fin.append_right,sortEval,iRV] using hs
  · exact fun h => ⟨h.1,(h.2.1 0).2⟩

theorem nonzeroDensityFormula_append (H : Set (Fin ((p+a)+1) → M))
    (z : Fin p → M) (x : Fin a → M) (y : Fin 1 → M) :
    Fin.append (Fin.append z x) y ∈ nonzeroDensityFormula H ↔
      Fin.append (Fin.append z x) y ∈ H ∧ y 0 ≠ iRVZero := by
  change (_ ∧ _) ↔ _
  change (_ ∧ Fin.append (Fin.append z x) y (Fin.natAdd (p+a) (0 : Fin 1)) ≠ iRVZero) ↔ _
  rw [Fin.append_right]

end IntegrationInACVF.Section7
