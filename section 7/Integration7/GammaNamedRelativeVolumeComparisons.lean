module

public import Integration7.GammaNamesGenericParameters
public import Integration7.OriginalBaseFiniteRelativeContractions

@[expose] public section
/-! Realizing original Gamma names in a containing small context does not
change the base of the resulting relative contraction comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_named_relative_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C₀ : BaseContext M)
    (hB₀ : B.real ⊆ (C₀.base : Set M)) (hBase : B.real = (C₀.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C₀.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ) :
    let C := gammaNamesContainingVolumeContext C₀ B hB₀ hgamma
    let hκ := C₀.uncountable.le
    let hs := C₀.saturated
    let hreal : Cardinal.mk B.real < C₀.κ := (Cardinal.mk_le_mk_of_subset hB₀).trans_lt C₀.small
    let hBC : B.real ⊆ (C.base : Set M) := fun _ hx =>
      gamma_names_containing_volume_context_contains C₀ B hB₀ hgamma (Or.inl (hB₀ hx))
    ∀ (U : DefSet (M := M) (C.base : Set M) (k+1) a) (V : DefSet (M := M) (C.base : Set M) (k+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (k+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ : Equiv.Perm (Fin (k+1))} (hi : UnaryRelative f (σ 0))
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε),
    let R := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hU hfinU T hT
    let S := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hV hfinV E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) k
        ⟨(gammaCoordinateDensityObject (e := k) (k := 0) hc C R (Set.Subset.refl _)
          (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ (fun q => (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero q ((hω q).trans hz))))).extend hCD,
          (gamma_coordinate_density_object_graphs hc C R (Set.Subset.refl _) _ _).extend hCD⟩
        ⟨(gammaCoordinateDensityObject (e := k) (k := 0) hc C S (Set.Subset.refl _)
          (FiniteRV.contractionOldLabelIndex E ε) (normalized_contraction_retained_density_nonzero E ε (fun q => (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero q ((hπ q).trans hz))))).extend hCD,
          (gamma_coordinate_density_object_graphs hc C S (Set.Subset.refl _) _ _).extend hCD⟩ := by
  intro C hκ hs hreal hBC U V hU hV hfinU hfinV f hf hfΓ ω π hm σ hi T E hT hE δ ε hω hπ
  exact finite_relative_volume_comparison_of_generic_extension hc C hκ hs hreal hBC hgamma γ hγ hγ1
    (fun x hx => gamma_names_context_preserves_independence hc C₀ B hB₀ hgamma hBase x hx)
    U V hU hV hfinU hfinV f hf hfΓ ω π hm hi T E hT hE δ ε hω hπ

end IntegrationInACVF.Section7
