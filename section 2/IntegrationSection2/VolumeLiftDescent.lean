import IntegrationSection2.GenericVolumeDescent
import IntegrationSection2.GammaVolumeDescent
import IntegrationSection2.VolumeBadLabels
import IntegrationSection2.ConcreteVolumeMorphisms
import Section9.GaussGraphConstruction

/-! Corollary 2.34 on the actual finite-volume categories. The
generic RV and pointwise Gamma conditions are proved separately.
The released predecessor's HenselizedGaussGraphInput, or its named
finite-extension reference, remains an explicit mathematical input.
Neither is an axiom of the model or a volume/Jacobian law assumed in
the definition of the conclusion. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms
open IntegrationInACVF.Section2.ConcreteVolumeMorphisms

namespace IntegrationInACVF.Section2.VolumeLiftDescent

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

theorem corollary_2_34_positive (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hk : 0 < k)
    {U V : RVFiniteObject (M := M) (C.base : Set M) k} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (hMeasure : PreservesOff ω π f) (hgraph : HenselizedGaussGraphInput (VFType (M := M))) :
    IsVolumeIsomorphism e ω π hU hV := by
  refine Or.inr ⟨?_,GammaVolumeDescent.pointwise_equation hc C e hU hV ω π f hf hlabel hMeasure hgraph⟩
  obtain ⟨D,_,hD,hEq⟩ := GenericVolumeDescent.generic_equation hc C hk e hU hV ω π f hf hlabel hMeasure hgraph
  refine ⟨VolumeBadLabels.labels U D,(VolumeBadLabels.dimension_le U D).trans_lt hD,fun u hu => ?_⟩
  exact hEq u (fun h => hu ((VolumeBadLabels.mem_labels U D u).mpr h))

theorem corollary_2_34_essential (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M)
    {U V : RVFiniteObject (M := M) (C.base : Set M) (k+1)}
    (e : RVFiniteEssentialIso U V) (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift (rvFiniteEssential U).obj) (rvLift (rvFiniteEssential V).obj))
    (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift (rvFiniteEssential U).obj,
      ((finiteVolumeProperty (C.base : Set M) (k+1)).ι.mapIso e).hom.map.graph p.val.2 (f p).val.2)
    (hMeasure : PreservesOff (essentialForm ω) (essentialForm π) f)
    (hgraph : HenselizedGaussGraphInput (VFType (M := M))) :
    IsVolumeIsomorphism e (essentialForm ω) (essentialForm π)
      (rvEssential_value_nonzero U.obj) (rvEssential_value_nonzero V.obj) :=
  corollary_2_34_positive hc C (Nat.succ_pos _) e
    (rvEssential_value_nonzero U.obj) (rvEssential_value_nonzero V.obj)
    (essentialForm ω) (essentialForm π) f hf hlabel hMeasure hgraph

theorem corollary_2_34_of_finite_extension_reference
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hk : 0 < k)
    {U V : RVFiniteObject (M := M) (C.base : Set M) k} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2)
    (hMeasure : PreservesOff ω π f) (hfinite : FiniteHenselianExtensionReference) :
    IsVolumeIsomorphism e ω π hU hV :=
  corollary_2_34_positive hc C hk e hU hV ω π f hf hlabel hMeasure
    (acvf_henselizedGaussGraphInput_of_finite_extension_reference hfinite)

end IntegrationInACVF.Section2.VolumeLiftDescent
