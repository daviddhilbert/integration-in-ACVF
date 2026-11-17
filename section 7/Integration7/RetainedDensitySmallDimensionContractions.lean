module

public import Integration7.RetainedDensityContractionObjects
public import Integration7.LiteralVolumeLiftMaps
public import Integration7.VolumeLiftFullDimension
public import Integration7.EssentialEmptyVolumeIsomorphisms
public import Integration7.GammaVolumeBlowupEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual specified contractions of any finite-label VF-small source
have empty essential volume objects. The density may vary with the old
RV labels, and both contraction orders are arbitrary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier GammaSetDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k m : ℕ} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (hGC : G.real ⊆ (C.base : Set M))
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) m)
variable (hA : GammaSetDefinable G (carrier A))
variable (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
variable (δ : Fin m) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
variable {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable G T.program)

def retainedDensityContractionLiftMap :
    Map (rawSpecialSet hc A)
      (rvVolumeLift (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val).domain :=
  (literalVolumeLiftMap hc
    (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val.underlying.obj
    (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
      (rawSpecialMap hc (typedContractionNaturalMap T))

theorem retained_density_contraction_lift_map_bijective :
    Function.Bijective (retainedDensityContractionLiftMap hκ hs hreal hc C hGC A hA hfin δ hδ T hT) :=
  (literalVolumeLiftMap_bijective hc
    (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val.underlying.obj
    (typedLift T.normalizedObject) (canonicalRVObject_presentsLift hc (normalizedTypedLift_presents T.normalizedObject))).comp
      (typedContractionNaturalMap_bijective T)

theorem retained_density_contraction_lift_dimension :
    vfDim (rawRVSpace (M := M) 1)
      (rvVolumeLift (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val).domain =
        vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) :=
  (vfDim_eq_of_bijective (rawRVSpace (M := M) 1)
    (retainedDensityContractionLiftMap hκ hs hreal hc C hGC A hA hfin δ hδ T hT)
    (retained_density_contraction_lift_map_bijective hκ hs hreal hc C hGC A hA hfin δ hδ T hT)).symm

theorem retained_density_contraction_essential_empty_of_small_dimension
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) < k+1) :
    (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT).val.essential.obj.domain.carrier = ∅ := by
  apply essential_empty_of_volume_lift_small_dimension hc C
  rw [retained_density_contraction_lift_dimension]
  exact hsmall

theorem small_dimension_retained_density_contractions_compare
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) < k+1)
    {τ : Equiv.Perm (Fin (k+1))} (E : StandardContraction A τ) (hE : GammaProgramDefinable G E.program) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) k
      (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ T hT)
      (retainedDensityContractionGammaObject hκ hs hreal hc C hGC A hA hfin δ hδ E hE) := by
  have hU := retained_density_contraction_essential_empty_of_small_dimension hκ hs hreal hc C hGC A hA hfin δ hδ T hT hsmall
  have hV := retained_density_contraction_essential_empty_of_small_dimension hκ hs hreal hc C hGC A hA hfin δ hδ E hE hsmall
  let e := RVVolumeIso.of_essential_empty hc C _ _ hU hV
  exact GammaVolumeBlowupEquivalent.of_iso C G e (gamma_volume_iso_of_essential_empty e hU)

end IntegrationInACVF.Section7
