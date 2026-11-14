import Integration7.GammaAbsoluteValues
import Integration7.FiniteVolumeIsoMaps
import Integration7.EssentialVolumeCoproduct

/-! Pointwise absolute Gamma weight and its upper cuts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "Abs" => MonoidWithZeroHom.ValueGroup₀
  (MonoidWithZeroHom.ofClass (Values.presentationValuation (M := M)))

def essentialGammaWeight (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : Abs :=
  RVOperations.absoluteHom (U.essentialForm.value u) *
    ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)

theorem essentialGammaWeight_ne_zero (U : PositiveRVVolumeObject (M := M) S k)
    (u : U.essential.obj.domain) : essentialGammaWeight U u ≠ 0 := by
  apply mul_ne_zero
  · exact (RVOperations.absolute_eq_zero _).not.mpr (U.essentialForm_nonzero u)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
      ((rv_nonzero_iff_raw _).mpr (U.essential_nonzero u i)))

theorem RVVolumeIso.essentialGammaWeight {U V : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V) (u : U.essential.obj.domain) :
    essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap f.iso u) := by
  have h := f.absolute_volumeRatio u
  rw [volumeRatio,map_div₀] at h
  have hV : RVOperations.absoluteHom (V.essentialForm.value (finiteIsoMap f.iso u)) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (V.essentialForm_nonzero _)
  have hU : (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
      ((rv_nonzero_iff_raw _).mpr (U.essential_nonzero u i)))
  exact ((div_eq_div_iff hV hU).mp h).trans (mul_comm _ _)

def essentialGammaUpperBound (U : PositiveRVVolumeObject (M := M) S k) (a : Abs) : Prop :=
  ∀ u : U.essential.obj.domain, essentialGammaWeight U u ≤ a

theorem RVVolumeIso.essentialGammaUpperBound {U V : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V) (a : Abs) :
    essentialGammaUpperBound U a ↔ essentialGammaUpperBound V a := by
  constructor
  · intro h v
    have hv := h (finiteIsoMap f.iso.symm v)
    rw [f.essentialGammaWeight,finiteIsoMap_apply_symm] at hv
    exact hv
  · intro h u
    rw [f.essentialGammaWeight]
    exact h _

theorem essentialGammaUpperBound_coprod (U V : PositiveRVVolumeObject (M := M) S k) (a : Abs) :
    essentialGammaUpperBound (U.coprod V) a ↔
      essentialGammaUpperBound U a ∧ essentialGammaUpperBound V a := by
  have hL (u : U.essential.obj.domain) :
      essentialGammaWeight (U.coprod V) (coprodEssentialLeftMap U V u) = essentialGammaWeight U u := by
    unfold essentialGammaWeight
    rw [coprodEssentialLeftMap_density,coprodEssentialLeftMap_coordinates]
  have hR (v : V.essential.obj.domain) :
      essentialGammaWeight (U.coprod V) (coprodEssentialRightMap U V v) = essentialGammaWeight V v := by
    unfold essentialGammaWeight
    rw [coprodEssentialRightMap_density,coprodEssentialRightMap_coordinates]
  constructor
  · intro h
    exact ⟨fun u => (hL u) ▸ h _, fun v => (hR v) ▸ h _⟩
  · rintro ⟨hU,hV⟩ w
    rcases coprodEssential_cover U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · rw [hL]; exact hU u
    · rw [hR]; exact hV v
end IntegrationInACVF.Section7
