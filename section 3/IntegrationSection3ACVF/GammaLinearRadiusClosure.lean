import IntegrationSection3ACVF.GammaLinearRestrictions

/-! Closedness from above of the actual linear-radius locus.
Overlapping concentric balls force every ordinary coefficient to agree;
pairwise radius density then gives the boundary ball itself. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaLinearRadiusClosure

open GammaRadiusAtomicity GammaLinearRestrictions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def locus (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) : Set (Values.Gamma (M := M)) :=
  {ρ | ∃ s, SlopeAt A f hfVF c ρ s}

theorem upward (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) (hρ : ρ ∈ locus A f hfVF c)
    (hρτ : ρ ≤ τ) : τ ∈ locus A f hfVF c := by
  obtain ⟨s,hs⟩ := hρ
  exact ⟨s,slope_mono A f hfVF c ρ τ s hρτ hs⟩

theorem closed_above (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (c : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hAll : ∀ τ, ρ < τ → τ ∈ locus A f hfVF c) : ρ ∈ locus A f hfVF c := by
  obtain ⟨τ0,hρτ0⟩ := exists_gt ρ
  obtain ⟨s0,hSlope0⟩ := hAll τ0 hρτ0
  have hSub : gammaBall c ρ true ⊆ A := by
    intro z hz
    let x : VFType (M := M) := ⟨z,hz.1⟩
    obtain ⟨τ,hρτ,hxτ⟩ := OpenRadiusLimits.exists_smaller_radius c x ρ hz
    obtain ⟨s,hSubτ,_⟩ := hAll τ hρτ
    exact hSubτ hxτ
  refine ⟨s0,hSub,?_⟩
  intro x y hx hy
  obtain ⟨τ,hρτ,hxτ,hyτ⟩ := OpenRadiusLimits.pair_smaller_radius c x y ρ hx hy
  obtain ⟨s,hSlope⟩ := hAll τ hρτ
  have hs : s = s0 := slope_unique A f hfVF c τ τ0 s s0 hSlope hSlope0
  obtain ⟨hSubτ,hLinear⟩ := hSlope
  subst s
  exact hLinear x y hxτ hyτ

end IntegrationInACVF.Section3ACVF.GammaLinearRadiusClosure
