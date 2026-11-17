module

public import Integration7.CanonicalContractionKeySquares
public import Integration7.GammaCoordinateDensityEquivalences
public import Integration7.RetainedDensityContractionObjects
public import Integration7.PullbackCoordinateVolumeObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The canonical finite contraction isomorphism preserves the full
volume tuple and every retained density. It therefore compares the
actual pullback volume object to the actual normalized contraction
volume object in a genuine small containing context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a : ℕ}

set_option maxHeartbeats 2200000 in
theorem canonical_pullback_contraction_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (k+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)
    (hVF : ∀ p : A, (T.naturalMap p).val.1 = p.val.1) (hcon : Contractible T.toMap) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ e : RVVolumeIso ((pullbackCoordinateVolumeObject hc A hAF δ hδ).extend hCD)
      ((retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val.extend hCD),
      e.GammaDefinable G := by
  let U := (FiniteRV.gammaPullbackAt hGC A hA hAF).toGamma
  let V := FiniteRV.gammaFiniteContraction hκ hs hreal hGC hA hfin T hT
  have hNZ : ∀ u : rvObjectDomain U.object, (u.val (Fin.natAdd (k+1) δ)).val ≠ iRVZero := by
    intro u
    obtain ⟨p,rfl⟩ := rawKeyImage_surjective A u
    erw [rawKeyMap_apply]
    simpa only [Fin.append_right] using hδ p
  let e := FiniteRV.gammaCanonicalContractionIso hκ hs hreal hGC hA hfin hAF T hT hVF hcon
  exact gamma_coordinate_density_equivalence_realize hc C U V (Set.Subset.refl _) (Set.Subset.refl _)
    (Fin.natAdd (k+1) δ) (FiniteRV.contractionOldLabelIndex T δ) hNZ
    (normalized_contraction_retained_density_nonzero T δ hδ) e
    (canonical_contraction_coordinates hκ hs hreal hGC hA hfin hAF T hT hVF hcon)
    (fun u => canonical_contraction_retained_labels hκ hs hreal hGC hA hfin hAF T hT hVF hcon u δ)

end IntegrationInACVF.Section7
