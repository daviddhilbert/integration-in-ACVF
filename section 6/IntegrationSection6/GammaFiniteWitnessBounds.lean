import IntegrationSection6.GammaWitnessUniformity
import Section3.GammaRVSeparation

/-! Bounded finite scalar witnesses over the original real/Gamma base.
Only the original names enter compactness; internal presentation codes
are not added to the saturation bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_uniform_finite_scalar_rows {B : Base (M := M)} {n : ℕ} {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sn : Fin n → SortTag) (σ : SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sn A) (R : Set ((Fin n → M) × M))
    (hR : DefinableOverBase B (Fin.lastCases σ sn) {z | (Fin.init z,z (Fin.last n)) ∈ R})
    (hfinite : ∀ a ∈ A, {x | (a,x) ∈ R}.Finite) :
    ∃ bound : ℕ, ∀ a ∈ A, {x | (a,x) ∈ R}.Finite ∧ {x | (a,x) ∈ R}.ncard ≤ bound := by
  have hNames := commonRealNames_small hκ B hreal hgamma
  have hAN := ((definableOver_iff_normalized_raw (commonRealNames B) sn A).mp hA.common_names).1
  have hRN := ((definableOver_iff_normalized_raw (commonRealNames B) (Fin.lastCases σ sn)
    {z | (Fin.init z,z (Fin.last n)) ∈ R}).mp hR.common_names).1
  have hRsum : @RawClosure.Tuple.RelationDefinable M N n (commonRealNames B) R := by
    letI := N
    let idx : Fin (n+1) → Fin n ⊕ Fin 1 := Fin.lastCases (Sum.inr 0) Sum.inl
    have hp := hRN.preimage_comp idx
    unfold RawClosure.Tuple.RelationDefinable
    convert hp using 1
    ext z
    change (z ∘ Sum.inl,z (Sum.inr 0)) ∈ R ↔ (Fin.init (z ∘ idx),(z ∘ idx) (Fin.last n)) ∈ R
    have hh : Fin.init (z ∘ idx) = z ∘ Sum.inl := by
      funext i
      change z (Fin.lastCases (Sum.inr 0) Sum.inl i.castSucc) = z (Sum.inl i)
      rw [Fin.lastCases_castSucc]
    rw [hh]
    simp only [Function.comp_apply,idx,Fin.lastCases_last]
  exact @RawClosure.Tuple.uniform_finite_rows M N n κ (@Saturated.normalize M sM κ hs)
    (commonRealNames B) hNames A hAN R hRsum hfinite

end IntegrationInACVF.Section6
