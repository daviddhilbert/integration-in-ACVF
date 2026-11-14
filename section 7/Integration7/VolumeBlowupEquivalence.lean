import Integration7.IteratedVolumeRefinement
import Integration7.GradedVolumeBlowups
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VolumeBlowupEquivalent.trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (g : VolumeBlowupEquivalent V W) : VolumeBlowupEquivalent U W := by
  obtain ⟨m, n, U₁, V₁, hU, hV₁, ⟨eUV⟩⟩ := h
  obtain ⟨p, q, V₂, W₁, hV₂, hW, ⟨eVW⟩⟩ := g
  obtain ⟨X, Y, hX, hY, ⟨eXY⟩⟩ := hV₁.common_refinement hc C hV₂
  obtain ⟨X', hX', ⟨eX'X⟩⟩ := hX.transport_source hc C eUV
  obtain ⟨Y', hY', ⟨eY'Y⟩⟩ := hY.transport_source hc C (eVW.symm hc C)
  exact ⟨m+p, q+n, X', Y', hU.trans hX', hW.trans hY',
    ⟨(eX'X.trans hc C eXY).trans hc C (eY'Y.symm hc C)⟩⟩

theorem muIsp_trans (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V W : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U V) (g : MuIsp (C.base : Set M) n V W) :
    MuIsp (C.base : Set M) n U W := by
  cases n with
  | zero =>
    obtain ⟨e⟩ := h
    obtain ⟨f⟩ := g
    exact ⟨e.trans f⟩
  | succ k => exact VolumeBlowupEquivalent.trans hc C h g

def muIspSetoid (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Setoid (RVVolumeObject (M := M) (C.base : Set M) n) where
  r := MuIsp (C.base : Set M) n
  iseqv := ⟨muIsp_refl hc C, muIsp_symm hc C, muIsp_trans hc C⟩
end IntegrationInACVF.Section7
