import Integration7.RVDensityRatioGraph

/-! In a canonical model, an actual real definable sorted formula is
an original-Gamma formula over the same real parameters. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section8

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem canonicalRawGammaFormula (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {n : ℕ} (sn : Fin n → SortTag) {A : Set (Fin n → M)}
    (hA : B.real.Definable LRV A) (hproper : ∀ x ∈ A, ∀ i, sortEval (sn i) (x i)) :
    DefinableOverBase B sn A := by
  have hN : @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin n) A :=
    Eq.mp (congrArg (fun I : LRV.Structure M =>
      @Set.Definable M (@Base.real M sM hM B) LRV I (Fin n) A)
      (normalize_eq_of_isCanonical hc).symm) hA
  exact real_definableOverBase B sn A ((definableOver_iff_normalized_raw B.real sn A).mpr ⟨hN,hproper⟩)

end IntegrationInACVF.Section7
