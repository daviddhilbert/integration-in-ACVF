import Integration7.GammaFunctionRowValidity
import Section4.RVCoordinates

/-! Recognize first-order function validity from typed RV functionality
and exact support. Proper-sort guards decode every raw witness. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sp : Fin p → SortTag}

theorem functionMapRowValid_of_typed
    {D : Set (Fin (p+a) → M)} {H : Set (Fin ((p+a)+b) → M)}
    (hD : DefinableOverBase B (Fin.append sp (fun _ : Fin a => .rv)) D)
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hfun : ∀ x : Fin a → CanonicalRV.RVSort M, Fin.append z (rvValues x) ∈ D →
      ∃! y : Fin b → CanonicalRV.RVSort M, Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ H)
    (hsupport : ∀ (x : Fin a → CanonicalRV.RVSort M) (y : Fin b → CanonicalRV.RVSort M),
      Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ H → Fin.append z (rvValues x) ∈ D) :
    functionMapRowValid sp D H z := by
  refine ⟨hz,?_,?_⟩
  · intro x hx
    have hxRV (i) : iRV (x i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hD.proper _ hx (Fin.natAdd p i)
    let xt : Fin a → CanonicalRV.RVSort M := fun i => ⟨x i,hxRV i⟩
    obtain ⟨y,hy,hu⟩ := hfun xt hx
    refine ⟨rvValues y,hy,?_⟩
    intro y' hy'
    have hyRV (i) : iRV (y' i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hH.proper _ hy' (Fin.natAdd (p+a) i)
    let yt : Fin b → CanonicalRV.RVSort M := fun i => ⟨y' i,hyRV i⟩
    exact congrArg rvValues (hu yt hy')
  · intro x y hxy
    have hxRV (i) : iRV (x i) := by
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hH.proper _ hxy
        (Fin.castAdd b (Fin.natAdd p i))
    have hyRV (i) : iRV (y i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hH.proper _ hxy (Fin.natAdd (p+a) i)
    exact hsupport (fun i => ⟨x i,hxRV i⟩) (fun i => ⟨y i,hyRV i⟩) hxy

end IntegrationInACVF.Section7
