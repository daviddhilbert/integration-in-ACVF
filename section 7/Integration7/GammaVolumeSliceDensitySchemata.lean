module

public import Integration7.LabelDensitySchemata
public import Integration7.UniformVolumeSchemaBounds
public import IntegrationSection6.GammaVolumeSliceSchemata

@[expose] public section

/-! RV volume slices retain the original object's density label. All
slice rows have finite fibres, and compactness supplies one valid bound
over the entire RV parameter space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e k : ℕ}

def gammaVolumeSliceDensitySchema (U : GammaRVFiniteObject B (e+(k+1)))
    (δ : Fin (rvObjectArity U.object)) :
    GammaRVVolumeSchema B e (rvObjectArity U.object) k (fun _ => .rv) :=
  labelDensitySchema (gammaVolumeSliceSchema U) δ

theorem gammaVolumeSliceDensitySchema_row
    (U : GammaRVFiniteObject B (e+(k+1))) (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (t : Fin e → RV (M := M)) (x : Fin (rvObjectArity U.object) → RV (M := M))
    (y : Fin 1 → RV (M := M)) :
    (gammaVolumeSliceDensitySchema U δ).rowDensity (rvValues t) x y ↔
      x ∈ (gammaVolumeSliceSchema U).rowDomain (rvValues t) ∧ y 0 = x δ := by
  rw [show (gammaVolumeSliceDensitySchema U δ).rowDensity (rvValues t) x y ↔
      x ∈ (gammaVolumeSliceSchema U).rowDomain (rvValues t) ∧
        y 0 = x δ ∧ (x δ).val ≠ iRVZero from
      labelDensitySchema_row (gammaVolumeSliceSchema U) δ (rvValues t)
        (fun i => (t i).property) x y]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨u, hu, _⟩ := (gammaVolumeSliceSchema_domain U t x).mp hx
    exact ⟨hx, hy, fun hz => hNZ u ((congrArg (fun v => (v δ).val) hu).trans hz)⟩

theorem gammaVolumeSliceDensitySchema_uniform_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U : GammaRVFiniteObject B (e+(k+1))) (δ : Fin (rvObjectArity U.object))
    (hNZ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero) :
    ∃ N : ℕ, ∀ t : Fin e → RV (M := M),
      ((gammaVolumeSliceDensitySchema U δ).withBound N).valid (rvValues t) := by
  let F := gammaVolumeSliceSchema U
  let A : Set (Fin e → M) := sortedUniverse (fun _ => .rv)
  have hA : DefinableOverBase B (fun _ : Fin e => .rv) A :=
    real_definableOverBase B _ _ (sortedUniverse_definable B.real _)
  have hF : ∀ z ∈ A, F.finiteRow z := by
    intro z hz
    let t : Fin e → RV (M := M) := fun i => ⟨z i,hz i⟩
    exact gammaVolumeSliceSchema_finiteRows U t
  obtain ⟨N, hN⟩ := finiteSchema_uniform_valid_bound hκ hs hreal hgamma F A hA hF
  refine ⟨N, fun t => ?_⟩
  have ht : rvValues t ∈ A := fun i => (t i).property
  change (labelDensitySchema (F.withBound N) δ).valid (rvValues t)
  apply labelDensitySchema_valid (F.withBound N) δ _ (hN _ ht)
  intro x
  obtain ⟨u, hu, _⟩ := (gammaVolumeSliceSchema_domain U t x.val).mp x.property
  exact fun hz => hNZ u ((congrArg (fun v => (v δ).val) hu).trans hz)

end IntegrationInACVF.Section7
