import IntegrationSection6.PointwiseRootEquations
import Section3.GammaSpecialization
import Section3.NormalizationSaturation

/-! A single original-real-base root equation works on the whole
Gamma-definable admissible label image. Temporary Gamma representatives
are used only in compactness and are absent from the resulting equation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_uniform_rootEquation {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {n : ℕ} (C : Set (Fin n → M)) (hC : DefinableOverBase B (fun _ => .rv) C) (j : Fin n)
    (hnz : ∀ t ∈ C, t j ≠ iRVZero)
    (halg : ∀ t : Fin n → CanonicalRV.RVSort M, rvValues t ∈ C →
      AlgebraicAtBase ⟨coordinateBase B.real j t,B.gamma⟩ .rv (t j).val) :
    ∃ R : Set (Fin n → M),
      @Set.Definable M B.real LRV (@CanonicalStructure.normalize M sM) (Fin n) R ∧
      C ⊆ @rootDomain M (@CanonicalStructure.normalize M sM) n R j := by
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  let hN := @CanonicalStructure.normalized_model M sM hM
  obtain ⟨k,c,hc⟩ := hC.specialize
  let T := B.real ∪ Set.range (rawTuple c)
  have hTC : @Set.Definable M T LRV N (Fin n) C :=
    ((definableOver_iff_normalized_raw T (fun _ => .rv) C).mp hc).1
  apply @exists_originalBase_rootSet M N n hN κ hs.normalize B.real T Set.subset_union_left
    (small_union_range hκ B.real hsmall (rawTuple c)) C hTC j
  intro t ht
  let tRV : Fin n → CanonicalRV.RVSort M := fun i => ⟨t i,hC.proper t ht i⟩
  have htzero : tRV j ≠ 0 := by
    intro he
    exact hnz t ht ((congrArg Subtype.val he).trans RVOperations.zero_val)
  obtain ⟨R,hR,hgood⟩ := exists_pointwise_rootEquation hκ hs h00 B hsmall hB
    Values.presentationValuation Values.presentation_compatible tRV j htzero (halg tRV ht)
  exact ⟨R,hR,hgood⟩

end IntegrationInACVF.Section6
