module

public import Integration7.CanonicalContractionNormalizationObjects
public import Integration7.LowerDimensionRVVolumeIsomorphisms
public import Integration7.ConstantCoordinateVolumeIsomorphisms
public import Integration7.GammaVolumeFullChartRestriction
public import Integration7.GammaRVMapGraphOperations
public import IntegrationSection6.GammaRawStandardContractions

@[expose] public section

/-! Actual contraction normalization preserves volume on an RV domain
of smaller dimension, in the same real presentation. Its complete
original-Gamma graph is the checked explicit volume-label projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {k a : ℕ}
variable {A : DefSet (M := M) S (k+1) a} {σ : Equiv.Perm (Fin (k+1))}

def rawUnitVolumeContraction (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres) :
    PositiveRVVolumeObject (M := M) S k := ⟨⟨canonicalRVObject hc C.contractionObject,hF⟩,VolumeForm.one _⟩

def normalizedUnitVolumeContraction (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres) :
    PositiveRVVolumeObject (M := M) S k := ⟨canonicalNormalizedFiniteContraction hc C hF,VolumeForm.one _⟩

def smallDimensionNormalizationVolumeIso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hd : rvDim (rawUnitVolumeContraction hc C hF).essential.obj.domain < k+1) :
    RVVolumeIso (rawUnitVolumeContraction hc C hF) (normalizedUnitVolumeContraction hc C hF) := by
  apply RVVolumeIso.of_gamma_product_of_lower_dimension (rvFiniteEssentialIso (canonicalFiniteNormalizationIso hc C hF))
    hd (fun _ => rfl)
  intro u
  have h := canonical_finite_normalization_volume hc C hF
    ⟨u.val,rvEssentialLabels_subset (canonicalRVObject hc C.contractionObject) u.property⟩
  exact (congrArg (fun z : Fin (k+1) → CanonicalRV.RVSort M => ∏ i, Values.vrv (z i)) h).symm

theorem canonical_finite_normalization_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hC : GammaSetDefinable P (carrier C.target)) :
    RVMapGamma (finiteIsoMap (canonicalFiniteNormalizationIso hc C hF)) P := by
  have h := gamma_rv_graph_of_global_formula
    (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex)
    (@rawRVProjectionMap M sM hM P.real C.arity ((k+1)+C.arity)
      (prependVolumeIndex C.volumeIndex) (PresentedSet.univ (SpecialTransformations.Section5.rawRVSpace C.arity) P.real))
    (gamma_raw_contraction_domain C hC) (fun _ => rfl)
  apply GammaGraphDefinable.congr h
  intro p q
  exact ⟨fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩,
    fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩⟩

theorem small_dimension_normalization_volume_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hd : rvDim (rawUnitVolumeContraction hc C hF).essential.obj.domain < k+1)
    (hPS : P.real ⊆ S) (hC : GammaSetDefinable P (carrier C.target)) :
    (smallDimensionNormalizationVolumeIso hc C hF hd).GammaDefinable P := by
  let U := rawUnitVolumeContraction hc C hF
  have hCoord : GammaGraphDefinable P (fun (p : Point (M := M) 0 U.underlying.obj.arity)
      (q : Point (M := M) 0 (k+1)) => U.underlying.obj.volume.graph p.2 q.2) := by
    apply GammaGraphDefinable.congr (gammaRawContractionObject C hPS hC).volume_graph
    intro p q
    exact ⟨fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩,
      fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩⟩
  exact gamma_volume_iso_of_full_map _ (finiteIsoMap (canonicalFiniteNormalizationIso hc C hF))
    (gamma_essential_volume_domain U hCoord) (canonical_finite_normalization_gamma hc C hF hC) (fun _ => rfl)

end IntegrationInACVF.Section7
