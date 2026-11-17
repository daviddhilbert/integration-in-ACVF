module

public import Integration7.RetainedDensityContractionObjects
public import Integration7.OriginalBaseRelativeVolumeComparisons
public import Integration7.MixedRetainedLabelVolumeForms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Arbitrary specified same-order contractions compare over the
original Gamma base with an arbitrary retained nonzero density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a : ℕ}

set_option maxHeartbeats 2000000 in
theorem retained_density_same_order_contractions_compare {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk G.real < κ) (hgamma : Cardinal.mk G.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (H : DefSet (M := M) (C.base : Set M) (k+1) a) (hH : GammaSetDefinable G (carrier H))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier H}.Finite)
    (δ : Fin a) (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (k+1))} (T E : StandardContraction H σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) k
        ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC H hH hfin δ hδ T hT).extend hCD)
        ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC H hH hfin δ hδ E hE).extend hCD) := by
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc H) δ hδ
  have hm : PreservesVFVolume ω ω (rawSpecialMap hc (Map.id H)) :=
    (vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ k) (rawSpecialMap hc (Map.id H))
      (fun _ => rfl)).mono (fun p h => ⟨1,h,by rw [RVOperations.rv_one,mul_one]; rfl⟩)
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hGC hGeneric H H hH hH hfin hfin (Map.id H) Function.bijective_id (gamma_identity_graph H hH)
    ω ω δ δ (fun _ => rfl) (fun _ => rfl) hm (unaryRelative_id (σ 0)) T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hGC H H hH hH hfin hfin
    T E hT hE δ δ hδ hδ hGeom

end IntegrationInACVF.Section7
