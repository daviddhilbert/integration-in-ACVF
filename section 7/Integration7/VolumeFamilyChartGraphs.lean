import Integration7.VolumeFamilyChartValues

/-! Uniform definability of the actual certified Jacobian graphs, with
arbitrary real parameter sorts. Finite unions of supports are definable. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {π : Type} {n : ℕ} {S : Set M}
local notation "I" => Fin (n+n)
local notation "O" => Fin 1
local notation "RV" => CanonicalRV.RVSort M

def volumeFamilyChartGraph (σ : VolumeChartSupport n) (C : Set (π ⊕ I → M)) :
    Set (π ⊕ (I ⊕ O) → M) :=
  {w | ∃ (t : I → RV) (ω : O → RV),
    rvValues t = w ∘ Sum.inr ∘ Sum.inl ∧ rvValues ω = w ∘ Sum.inr ∘ Sum.inr ∧
    VolumeChartValue σ (volumeFamilyRow C (w ∘ Sum.inl)) t ω}

private theorem familyChartTuple_eq (w : π ⊕ (I ⊕ O) → M) (t : I → RV) (ω : O → RV)
    (ht : rvValues t = w ∘ Sum.inr ∘ Sum.inl)
    (hω : rvValues ω = w ∘ Sum.inr ∘ Sum.inr) :
    Sum.elim (w ∘ Sum.inl) (Sum.elim (rvValues t) (rvValues ω)) = w := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · exact congrFun ht i
  · exact congrFun hω i

theorem volumeFamilyChartGraph_definable [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) :
    S.Definable LRV (volumeFamilyChartGraph σ C) := by
  obtain ⟨T,hT⟩ := exists_rv_scale_ratio_term (M := M) (n := n)
  have he : volumeFamilyChartGraph σ C = rawVolumeFamilyChartValue σ C T := by
    ext w
    constructor
    · rintro ⟨t,ω,ht,hω,hJ⟩
      have h := (mem_rawVolumeFamilyChartValue σ C T hT (w ∘ Sum.inl) t ω).mpr hJ
      exact familyChartTuple_eq w t ω ht hω ▸ h
    · intro h
      obtain ⟨t,ht⟩ := h.1
      obtain ⟨ω,hω⟩ := h.2.1
      exact ⟨t,ω,ht,hω,(mem_rawVolumeFamilyChartValue σ C T hT (w ∘ Sum.inl) t ω).mp
        ((familyChartTuple_eq w t ω ht hω).symm ▸ h)⟩
  rw [he]
  exact rawVolumeFamilyChartValue_definable hc σ hC T

theorem volumeFamilyChartGraphUnion_definable [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : Finset (VolumeChartSupport n))
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) :
    S.Definable LRV {w | ∃ σ ∈ A, w ∈ volumeFamilyChartGraph σ C} := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have h : S.Definable LRV (∅ : Set (π ⊕ (I ⊕ O) → M)) := Set.definable_empty
    convert h using 1
    ext w
    simp only [Finset.notMem_empty,false_and,exists_false,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
  | insert σ A hσ ih =>
    convert (volumeFamilyChartGraph_definable hc σ hC).union ih using 1
    ext w
    simp only [Finset.mem_insert,or_and_right,exists_or,exists_eq_left,
      Set.mem_union,Set.mem_ofPred_eq]

end IntegrationInACVF.Section7
