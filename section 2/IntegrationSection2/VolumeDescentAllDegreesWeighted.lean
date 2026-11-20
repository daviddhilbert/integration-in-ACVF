import IntegrationSection2.VolumeDescentAllDegrees
import IntegrationSection2.WeightedZeroVolumeDescent

/-! Corollary 2.34 in all degrees with the corrected weighted degree zero.

The legacy `VolumeDescentAllDegrees.corollary_2_34_all_degrees` concludes
`True` in degree zero, where its form type is `PUnit`. This additive
statement replaces that branch by the actual weighted measured-zero result
`WeightedZeroVolumeDescent.corollary_2_34_zero_weighted`: the supplied label
isomorphism together with the determinant-one measure equation gives an
isomorphism in the corrected measured degree-zero category whose map is the
supplied label map. Positive degrees are exactly the legacy branch. -/

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.Section10 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms
open IntegrationInACVF.Section2.ConcreteVolumeMorphisms

namespace IntegrationInACVF.Section2.VolumeDescentAllDegrees

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Corollary 2.34 in every degree. Degree zero is the corrected weighted
measured-zero statement (`corollary_2_34_zero_weighted`); every positive
degree `j+1` is the branch of `corollary_2_34_all_degrees`. -/
theorem corollary_2_34_all_degrees_weighted (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) :
    (∀ {U V : MeasuredRVZero (M := M) (C.base : Set M) rvVolumeScale}
      (e : U.underlying ≅ V.underlying)
      (f : Map (rvLift U.underlying.obj) (rvLift V.underlying.obj)),
      (∀ p, liftLabelMap V.underlying.obj (f p) =
        WeightedZeroVolumeDescent.labelMap e (liftLabelMap U.underlying.obj p)) →
      (∀ p, ∃ J : VFType (M := M), HasMixedVFJacobianAt f p J ∧
        (U.lift hc).weight p = (V.lift hc).weight (f p) * CanonicalRV.encodedRv J) →
      ∃ i : U ≅ V, i.hom.map = WeightedZeroVolumeDescent.labelMap e) ∧
    (∀ {j : ℕ} {U V : RVFiniteObject (M := M) (C.base : Set M) (j+1)}
      (e : RVFiniteEssentialIso U V) (ω : Form U) (π : Form V)
      (f : Map (rvLift (rvFiniteEssentialPart U).obj) (rvLift (rvFiniteEssentialPart V).obj)),
      Function.Bijective f →
      (∀ p : rvLift (rvFiniteEssentialPart U).obj,
        ((finiteVolumeProperty (C.base : Set M) (j+1)).ι.mapIso e).hom.map.graph
          p.val.2 (f p).val.2) →
      PreservesLift ω π f → IsVolumeIsomorphism e ω π) :=
  ⟨fun e f hlabel hMeasure =>
      ⟨WeightedZeroVolumeDescent.corollary_2_34_zero_weighted hc e f hlabel hMeasure,
        WeightedZeroVolumeDescent.corollary_2_34_zero_weighted_map hc e f hlabel hMeasure⟩,
    fun e ω π f hf hlabel hMeasure =>
      corollary_2_34_all_degrees hc C e ω π f hf hlabel hMeasure⟩

end IntegrationInACVF.Section2.VolumeDescentAllDegrees
