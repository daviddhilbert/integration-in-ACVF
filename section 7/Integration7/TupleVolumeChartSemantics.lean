import Integration7.WeightedJacobianSemantics

/-! The tuple chart formula has the actual residue-Jacobian chart semantics
on typed RV inputs. No representatives or additional parameters are used. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p d : ℕ}

theorem rvValues_productTuple_eq_append (u v : Fin d → CanonicalRV.RVSort M) :
    rvValues (productTuple u v) = Fin.append (rvValues u) (rvValues v) := by
  apply productTuple_ext
  · intro i
    change (productTuple u v (productLeft d d i)).val = _
    rw [productTuple_left]
    change (u i).val = Fin.append (rvValues u) (rvValues v) (Fin.castAdd d i)
    rw [Fin.append_left]
    rfl
  · intro i
    change (productTuple u v (productRight d d i)).val = _
    rw [productTuple_right]
    change (v i).val = Fin.append (rvValues u) (rvValues v) (Fin.natAdd d i)
    rw [Fin.append_right]
    rfl

theorem tupleVolumeChartGraph_append (σ : VolumeChartSupport d)
    (C : Set (Fin (p+(d+d)) → M)) (z : Fin p → M)
    (t : Fin (d+d) → CanonicalRV.RVSort M) (ω : Fin 1 → CanonicalRV.RVSort M) :
    Fin.append (Fin.append z (rvValues t)) (rvValues ω) ∈ tupleVolumeChartGraph σ C ↔
      VolumeChartValue σ {r | Fin.append z (rvValues r) ∈ C} t ω := by
  rw [mem_tupleVolumeChartGraph]
  simp only [Fin.append_left,Fin.append_right]
  constructor
  · rintro ⟨t',ω',ht,hω,hJ⟩
    have ht' : t' = t := rvValues_injective ht
    have hω' : ω' = ω := rvValues_injective hω
    exact ht' ▸ hω' ▸ hJ
  · intro hJ
    exact ⟨t,ω,rfl,rfl,hJ⟩

theorem supportedSchemaJacobianFormula_typed_iff
    {B : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    {a b k : ℕ} {sp : Fin p → SortTag}
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (H : Set (Fin ((p+a)+b) → M)) (A : Finset (VolumeChartSupport (k+1)))
    (z : Fin p → M) (u v : Fin (k+1) → CanonicalRV.RVSort M)
    (φ ψ : CanonicalRV.RVSort M) (hz : ∀ i, sortEval (sp i) (z i))
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    weightedPairTuple z (rvValues u) (rvValues v) (fun _ : Fin 1 => φ.val) (fun _ : Fin 1 => ψ.val) ∈
      supportedSchemaJacobianFormula F G H A ↔
    ∃ σ ∈ A, VolumeChartValue σ
      {r | Fin.append z (rvValues r) ∈ schemaVolumeCorrespondence F.object G.object H}
      (productTuple u v) (fun _ => φ / ψ) := by
  unfold supportedSchemaJacobianFormula
  rw [weightedJacobianFormula_typed_iff sp _ z u v φ ψ hz hφ hψ]
  change (∃ σ ∈ A, _) ↔ _
  apply exists_congr
  intro σ
  apply and_congr_right
  intro _
  rw [← rvValues_productTuple_eq_append]
  change (Fin.append (Fin.append z (rvValues (productTuple u v)))
      (rvValues (fun _ : Fin 1 => φ / ψ)) ∈ tupleVolumeChartGraph σ _) ↔ _
  exact tupleVolumeChartGraph_append σ _ z _ _

end IntegrationInACVF.Section7
