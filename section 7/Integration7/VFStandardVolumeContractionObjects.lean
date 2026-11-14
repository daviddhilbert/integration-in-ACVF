import Integration7.PositiveSelectedLemma75
import Integration7.ContractionRetainedDensityLabels
import Integration7.GammaVolumeSliceAssemblyGeometry
import IntegrationSection6.FiniteStandardContractions

/-! Standard contraction objects of arbitrary positive VF volume
objects. The density graph retains the density as an old RV coordinate;
only the contracted VF tags form the final volume tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (GammaRVFiniteObject rvObjectDomain rvObjectArity gammaLogicInput carrier setDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {k : ℕ}

def PositiveVFVolumeObject.gammaStandardContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    GammaRVFiniteObject (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (k+1) :=
  FiniteRV.gammaFiniteContraction C.uncountable.le C.saturated C.small (Set.Subset.refl _)
    ((gammaLogicInput ⟨(C.base : Set M),Ξ⟩).real_set _ (setDefinable _))
    U.densityGraph.finite_labels T (gamma_program_over_real_base ⟨(C.base : Set M),Ξ⟩ T.program)

theorem PositiveVFVolumeObject.standardContractionDensity_nonzero
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    ∀ u : rvObjectDomain (U.gammaStandardContraction hc Ξ T).object,
      (u.val (FiniteRV.contractionOldLabelIndex T (Fin.last U.arity))).val ≠ iRVZero := by
  apply normalized_contraction_retained_density_nonzero T (Fin.last U.arity)
  intro q
  apply (rv_nonzero_iff_raw _).mp
  intro h
  exact U.densityGraph.form.nonzero ⟨q.val,q.property⟩
    ((densityGraph_form_last U ⟨q.val,q.property⟩).trans h)

def PositiveVFVolumeObject.standardContractionObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  gammaCoordinateDensityObject (e := k) (k := 0) hc C (U.gammaStandardContraction hc Ξ T)
    (Set.Subset.refl _) (FiniteRV.contractionOldLabelIndex T (Fin.last U.arity))
    (U.standardContractionDensity_nonzero hc Ξ T)

theorem PositiveVFVolumeObject.standardContractionObject_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ) :
    VolumeObjectGamma (U.standardContractionObject hc C Ξ T) ⟨(C.base : Set M),Ξ⟩ :=
  gamma_coordinate_density_object_graphs (M := M) (B := ⟨(C.base : Set M),Ξ⟩) (e := k) (k := 0)
    hc C (U.gammaStandardContraction hc Ξ T) (Set.Subset.refl _)
    (FiniteRV.contractionOldLabelIndex T (Fin.last U.arity)) (U.standardContractionDensity_nonzero hc Ξ T)

end IntegrationInACVF.Section7
