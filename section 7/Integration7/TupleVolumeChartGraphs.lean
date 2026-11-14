import Integration7.VolumeFamilyChartGraphs

/-! Finite-tuple formulas for volume chart values. This repackages the
parameterized chart graph without choosing Gamma representatives. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {π : Type} {p n : ℕ}
local notation "I" => Fin (n+n)
local notation "RV" => CanonicalRV.RVSort M

def tupleVolumeFamily (C : Set (Fin (p+(n+n)) → M)) : Set (Fin p ⊕ I → M) :=
  {w | Fin.append (w ∘ Sum.inl) (w ∘ Sum.inr) ∈ C}

private def tupleChartCoordinates (p n : ℕ) :
    Fin p ⊕ (Fin (n+n) ⊕ Fin 1) → Fin ((p+(n+n))+1) :=
  Sum.elim (fun i => Fin.castAdd 1 (Fin.castAdd (n+n) i))
    (Sum.elim (fun i => Fin.castAdd 1 (Fin.natAdd p i)) (Fin.natAdd (p+(n+n))))

def tupleVolumeChartGraph (σ : VolumeChartSupport n) (C : Set (Fin (p+(n+n)) → M)) :
    Set (Fin ((p+(n+n))+1) → M) :=
  {w | w ∘ tupleChartCoordinates p n ∈ volumeFamilyChartGraph σ (tupleVolumeFamily C)}

theorem mem_tupleVolumeChartGraph (σ : VolumeChartSupport n)
    (C : Set (Fin (p+(n+n)) → M)) (w : Fin ((p+(n+n))+1) → M) :
    w ∈ tupleVolumeChartGraph σ C ↔ ∃ (t : I → RV) (ω : Fin 1 → RV),
      rvValues t = (fun i => w (Fin.castAdd 1 (Fin.natAdd p i))) ∧
      rvValues ω = (fun i => w (Fin.natAdd (p+(n+n)) i)) ∧
      VolumeChartValue σ {r | Fin.append
        (fun i => w (Fin.castAdd 1 (Fin.castAdd (n+n) i))) (rvValues r) ∈ C} t ω := Iff.rfl

theorem tupleVolumeChartGraph_uniform [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    {S : Set M} {R : Set (π ⊕ Fin (p+(n+n)) → M)} (hR : S.Definable LRV R) :
    S.Definable LRV {w : π ⊕ Fin ((p+(n+n))+1) → M |
      w ∘ Sum.inr ∈ tupleVolumeChartGraph σ {x | Sum.elim (w ∘ Sum.inl) x ∈ R}} := by
  let i : π ⊕ Fin (p+(n+n)) → (π ⊕ Fin p) ⊕ I :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Fin.addCases (Sum.inl ∘ Sum.inr) Sum.inr)
  let j : ((π ⊕ Fin p) ⊕ (I ⊕ Fin 1)) → π ⊕ Fin ((p+(n+n))+1) :=
    Sum.elim (Sum.elim Sum.inl (fun q => Sum.inr (tupleChartCoordinates p n (.inl q))))
      (fun q => Sum.inr (tupleChartCoordinates p n (.inr q)))
  let E : Set ((π ⊕ Fin p) ⊕ I → M) := {w | w ∘ i ∈ R}
  have h := (volumeFamilyChartGraph_definable hc σ (hR.preimage_comp i)).preimage_comp j
  convert h using 1
  ext w
  have hrow :
      {r : I → RV | Fin.append
        (fun q => w (.inr (Fin.castAdd 1 (Fin.castAdd (n+n) q)))) (rvValues r) ∈
          {x | Sum.elim (w ∘ Sum.inl) x ∈ R}} =
      volumeFamilyRow E ((w ∘ j) ∘ Sum.inl) := by
    ext r
    change (Sum.elim (w ∘ Sum.inl) (Fin.append
      (fun q => w (.inr (Fin.castAdd 1 (Fin.castAdd (n+n) q)))) (rvValues r)) ∈ R) ↔
      (Sum.elim ((w ∘ j) ∘ Sum.inl) (rvValues r) ∘ i ∈ R)
    apply Iff.of_eq
    apply congrArg (fun q => q ∈ R)
    funext q
    cases q with
    | inl q => rfl
    | inr q =>
      refine Fin.addCases (fun q => ?_) (fun q => ?_) q
      · simp only [i,j,Function.comp_apply,Sum.elim_inr,Sum.elim_inl,
          Fin.append_left,Fin.addCases_left,tupleChartCoordinates]
      · simp only [i,j,Function.comp_apply,Sum.elim_inr,Sum.elim_inl,
          Fin.append_right,Fin.addCases_right,tupleChartCoordinates]
  change (w ∘ Sum.inr ∈ tupleVolumeChartGraph σ {x | Sum.elim (w ∘ Sum.inl) x ∈ R}) ↔
    (w ∘ j ∈ volumeFamilyChartGraph σ E)
  rw [mem_tupleVolumeChartGraph]
  change (∃ t ω, _ ∧ _ ∧ VolumeChartValue σ _ t ω) ↔
    (∃ t ω, _ ∧ _ ∧ VolumeChartValue σ _ t ω)
  simp only [Function.comp_apply] at hrow ⊢
  rw [hrow]
  rfl

theorem tupleVolumeChartGraph_proper (σ : VolumeChartSupport n)
    (sp : Fin p → SortTag) (C : Set (Fin (p+(n+n)) → M))
    (hC : ∀ x ∈ C, ∀ i, sortEval (Fin.append sp (fun _ : I => SortTag.rv) i) (x i)) :
    ∀ w ∈ tupleVolumeChartGraph σ C, ∀ i,
      sortEval (Fin.append (Fin.append sp (fun _ : I => SortTag.rv)) (fun _ : Fin 1 => .rv) i) (w i) := by
  intro w hw
  obtain ⟨t,ω,ht,hω,hJ⟩ := (mem_tupleVolumeChartGraph σ C w).mp hw
  have hmem : t ∈ {r | Fin.append
      (fun q => w (Fin.castAdd 1 (Fin.castAdd (n+n) q))) (rvValues r) ∈ C} := by
    obtain ⟨a,b,c,z,_,_,_,hz,_,he,_⟩ := hJ
    exact he ▸ hz.1
  intro q
  refine Fin.addCases (fun q => ?_) (fun q => ?_) q
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) q
    · simpa only [Fin.append_left] using hC _ hmem (Fin.castAdd (n+n) q)
    · have he : (t q).val = w (Fin.castAdd 1 (Fin.natAdd p q)) := congrFun ht q
      have hv : iRV (w (Fin.castAdd 1 (Fin.natAdd p q))) := he ▸ (t q).property
      simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hv
  · have he : (ω q).val = w (Fin.natAdd (p+(n+n)) q) := congrFun hω q
    have hv : iRV (w (Fin.natAdd (p+(n+n)) q)) := he ▸ (ω q).property
    simpa only [Fin.append_right,sortEval,iRV] using hv

end IntegrationInACVF.Section7
