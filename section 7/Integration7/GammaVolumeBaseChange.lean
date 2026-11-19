import Integration7.GammaVolumeBlowupEquivalence
import Integration7.GammaChartedVolumeBlowups
import Integration7.CommonContextVolumeEquivalences

/-! Change of Gamma base for Gamma volume certificates. When every real name of a base
`B'` is in the definable closure of `B` and its Gamma names lie in `B`, Gamma volume
objects, blowups, isomorphisms and blowup equivalences over `B'` are Gamma over `B`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B B' : Base (M := M)} {S : Set M} {k : ℕ}

/-- `B'` is dominated by `B`: its real names are definable over `B`, its Gamma names lie in `B`. -/
structure GammaBaseDominated (B' B : Base (M := M)) : Prop where
  real : ∀ c ∈ B'.real, ∃ σ, DefinableClosureAtBase B σ c
  gamma : B'.gamma ⊆ B.gamma

theorem GammaBaseDominated.of_subset (hr : B'.real ⊆ B.real) (hg : B'.gamma ⊆ B.gamma) :
    GammaBaseDominated B' B :=
  ⟨fun _ hc => (subset_closureBase B).1 (hr hc),hg⟩

theorem GammaBaseDominated.definable (h : GammaBaseDominated B' B) {n : ℕ} {sn : Fin n → SortTag}
    {U : Set (Fin n → M)} (hU : DefinableOverBase B' sn U) : DefinableOverBase B sn U :=
  hU.eliminate_definable_params h.real (fun γ hγ => gamma_name_definable B γ (h.gamma hγ))

theorem GammaBaseDominated.set (h : GammaBaseDominated B' B) {n m : ℕ} {X : Set (Point (M := M) n m)}
    (hX : GammaSetDefinable B' X) : GammaSetDefinable B X := h.definable hX

theorem GammaBaseDominated.graph (h : GammaBaseDominated B' B) {n m u w : ℕ}
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable B' r) : GammaGraphDefinable B r := h.definable hr

theorem VolumeObjectGamma.changeBase {U : PositiveRVVolumeObject (M := M) S k}
    (hU : VolumeObjectGamma U B') (h : GammaBaseDominated B' B) : VolumeObjectGamma U B :=
  ⟨h.graph hU.coordinates,h.graph hU.density⟩

theorem GammaBlowupCenter.changeBase {U : PositiveRVVolumeObject (M := M) S k}
    (hU : GammaBlowupCenter U B') (h : GammaBaseDominated B' B) : GammaBlowupCenter U B := by
  intro u
  apply (hU u).eliminate_definable_params
  · rintro c (hc | hc)
    · obtain ⟨σ,hσ⟩ := h.real c hc
      exact ⟨σ,DefinableAtBase.mono hσ Set.subset_union_left (Set.Subset.refl _)⟩
    · exact (subset_closureBase _).1 (Or.inr hc)
  · intro γ hγ
    exact gamma_name_definable _ γ (h.gamma hγ)

theorem VolumeBlowup.GammaDefinable.changeBase {U W : PositiveRVVolumeObject (M := M) S k}
    {b : VolumeBlowup U W} (hb : b.GammaDefinable B') (h : GammaBaseDominated B' B) : b.GammaDefinable B :=
  ⟨hb.locus.changeBase h,hb.complement.changeBase h,hb.blown.changeBase h,h.graph hb.elementary,
    hb.centerAlgebraic.changeBase h,h.graph hb.source,h.graph hb.target⟩

/-- Rebase a Gamma volume object along a dominated base. -/
def GammaVolumeObjects.changeBase (U : GammaVolumeObjects B' S k) (h : GammaBaseDominated B' B) :
    GammaVolumeObjects B S k := ⟨U.val,U.property.changeBase h⟩

theorem GammaIteratedVolumeBlowup.changeBase (h : GammaBaseDominated B' B) {n : ℕ}
    {U V : GammaVolumeObjects B' S k} (hUV : GammaIteratedVolumeBlowup B' S k n U V) :
    GammaIteratedVolumeBlowup B S k n (U.changeBase h) (V.changeBase h) := by
  induction hUV with
  | refl U => exact .refl _
  | @step n U V W hb _ ih =>
    obtain ⟨b,hb⟩ := hb
    exact .step (V := V.changeBase h) ⟨b,hb.changeBase h⟩ ih

theorem GammaVolumeBlowupEquivalent.changeBase (h : GammaBaseDominated B' B)
    {U V : GammaVolumeObjects B' S k} (hUV : GammaVolumeBlowupEquivalent B' S k U V) :
    GammaVolumeBlowupEquivalent B S k (U.changeBase h) (V.changeBase h) := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := hUV
  exact ⟨m,n,U'.changeBase h,V'.changeBase h,hU.changeBase h,hV.changeBase h,e,h.graph he⟩

/-- Base change for equivalences of objects already carrying certificates over the smaller base. -/
theorem GammaVolumeBlowupEquivalent.of_changeBase (h : GammaBaseDominated B' B)
    {U V : GammaVolumeObjects B S k} (hU : VolumeObjectGamma U.val B') (hV : VolumeObjectGamma V.val B')
    (hUV : GammaVolumeBlowupEquivalent B' S k ⟨U.val,hU⟩ ⟨V.val,hV⟩) :
    GammaVolumeBlowupEquivalent B S k U V :=
  hUV.changeBase h

end IntegrationInACVF.Section7
