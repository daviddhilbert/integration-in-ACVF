module

public import Integration7.OriginalBaseRelativeVolumeComparisons
public import Integration7.GeometricFiniteStandardVolumeComparisons

@[expose] public section
/-! Compare specified normalized contraction volume objects over the original
Gamma base, including real presentation contexts that preserve VF independence. -/
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
theorem finite_relative_volume_comparison_of_generic_extension {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (U : DefSet (M := M) (C.base : Set M) (k+1) a) (V : DefSet (M := M) (C.base : Set M) (k+1) b)
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
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε) :
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
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma
    γ hγ hγ1 hBC hGeneric U V hU hV hfinU hfinV f hf hfΓ ω π δ ε hω hπ hm hi T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hBC
    U V hU hV hfinU hfinV T E hT hE δ ε
    (fun q => (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero q ((hω q).trans hz)))
    (fun q => (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero q ((hπ q).trans hz))) hGeom

end IntegrationInACVF.Section7
