import IntegrationSection2.VolumeLiftDescent
import IntegrationSection2.ConstructedGaussGraph

/-! Corollary 2.34 with all predecessor graph/reference obligations
supplied by checked proofs. In positive degree the main theorem uses
the actual essential parts of arbitrary original finite-volume RV
objects. Degree zero is the already recorded convention mRV[0]=RV[0]. -/

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms
open IntegrationInACVF.Section2.ConcreteVolumeMorphisms

namespace IntegrationInACVF.Section2

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

theorem corollary_2_34_nonzero (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (hk : 0 < k)
    {U V : RVFiniteObject (M := M) (C.base : Set M) k} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero)
    (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift U.obj) (rvLift V.obj)) (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U.obj, ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph
      p.val.2 (f p).val.2) (hMeasure : PreservesOff ω π f) :
    IsVolumeIsomorphism e ω π hU hV :=
  VolumeLiftDescent.corollary_2_34_positive hc C hk e hU hV ω π f hf hlabel hMeasure
    ConstructedGaussGraph.acvf_graph_input

theorem corollary_2_34 (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M)
    {U V : RVFiniteObject (M := M) (C.base : Set M) (k+1)}
    (e : RVFiniteEssentialIso U V) (ω : RVForm U) (π : RVForm V)
    (f : Map (rvLift (rvFiniteEssential U).obj) (rvLift (rvFiniteEssential V).obj))
    (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift (rvFiniteEssential U).obj,
      ((finiteVolumeProperty (C.base : Set M) (k+1)).ι.mapIso e).hom.map.graph p.val.2 (f p).val.2)
    (hMeasure : PreservesOff (essentialForm ω) (essentialForm π) f) :
    IsVolumeIsomorphism e (essentialForm ω) (essentialForm π)
      (rvEssential_value_nonzero U.obj) (rvEssential_value_nonzero V.obj) :=
  VolumeLiftDescent.corollary_2_34_essential hc C e ω π f hf hlabel hMeasure
    ConstructedGaussGraph.acvf_graph_input

end IntegrationInACVF.Section2
