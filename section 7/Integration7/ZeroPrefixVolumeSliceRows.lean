import Integration7.GammaVolumeSliceDensityAssembly
import Integration7.VolumeSchemaRowSemantics

/-! A zero-prefix slice is the whole unary volume object, with its full
coordinate and density graphs. No volume coordinate is discarded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem gamma_zero_prefix_density_schema_row
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B 1) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (N : ℕ) (t : Fin 0 → RV (M := M)) :
    RVVolumeSchemaRow (gammaCoordinateDensityObject (e := 0) (k := 0) hc C U hUC δ hδ)
      ((gammaVolumeSliceDensitySchema (e := 0) (k := 0) U δ).withBound N) (rvValues t) := by
  have hAppend (y : Fin 1 → RV (M := M)) : Fin.append t y = y := by
    funext i
    simpa using Fin.append_right t y i
  constructor
  · intro x y
    change (gammaVolumeSliceSchema (e := 0) (k := 1) U).rowVolume (rvValues t) x y ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ gammaVolumeValue U.toGammaRVObject u = y
    exact (gammaVolumeSliceSchema_volume U t x y).trans (by rw [hAppend])
  · intro x w
    change (gammaVolumeSliceDensitySchema (e := 0) (k := 0) U δ).rowDensity (rvValues t) x w ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ (fun _ : Fin 1 => u.val δ) = w
    refine Iff.trans (gammaVolumeSliceDensitySchema_row (M := M) (B := B) (e := 0) (k := 0)
      U δ hδ t x w) ?_
    constructor
    · rintro ⟨hx,hw⟩
      obtain ⟨u,hu,_⟩ := (gammaVolumeSliceSchema_domain (M := M) (B := B) (e := 0) (k := 1) U t x).mp hx
      refine ⟨⟨u.val,u.property⟩,hu,?_⟩
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (congrArg (fun r => r δ) hu).trans hw.symm
    · rintro ⟨u,hu,hw⟩
      refine ⟨(gammaVolumeSliceSchema_domain (M := M) (B := B) (e := 0) (k := 1) U t x).mpr ⟨⟨u.val,u.property⟩,hu,Subsingleton.elim _ _⟩,?_⟩
      exact (congrFun hw 0).symm.trans (congrArg (fun r => r δ) hu)

end IntegrationInACVF.Section7
