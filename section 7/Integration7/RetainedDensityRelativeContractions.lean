module

public import Integration7.RetainedDensitySameOrderContractions

@[expose] public section

/-! Corollary7.6 for specified relatively unary Jacobian-one maps,
with an arbitrary literal retained density on each side. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a b : ℕ}

set_option maxHeartbeats 2200000 in
theorem retained_density_relative_contractions_compare {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk G.real < κ) (hgamma : Cardinal.mk G.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (U : DefSet (M := M) (C.base : Set M) (k+1) a)
    (V : DefSet (M := M) (C.base : Set M) (k+1) b)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (hfinU : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (k+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable G (pointMapGraph f))
    (hLabels : ∀ p : U, (f p).val.2 ε = p.val.2 δ)
    (hJ : VFAlmostEverywhere (rawSpecialSet hc U)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    {σ : Equiv.Perm (Fin (k+1))} (hi : UnaryRelative f (σ 0))
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) k
        ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC U hU hfinU δ hδ T hT).extend hCD)
        ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC V hV hfinV ε hε E hE).extend hCD) := by
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc U) δ hδ
  let π := mixedRetainedLabelVolumeForm (rawSpecialSet hc V) ε hε
  have hm : PreservesVFVolume ω π (rawSpecialMap hc f) := by
    apply hJ.mono
    intro p hp
    refine ⟨1,hp,?_⟩
    rw [RVOperations.rv_one,mul_one]
    exact (hLabels p).symm
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hGC hGeneric U V hU hV hfinU hfinV f hf hfΓ ω π δ ε (fun _ => rfl) (fun _ => rfl) hm hi T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hGC U V hU hV hfinU hfinV
    T E hT hE δ ε hδ hε hGeom

end IntegrationInACVF.Section7
