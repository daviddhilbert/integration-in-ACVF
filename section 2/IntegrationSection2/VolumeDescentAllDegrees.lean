import IntegrationSection2.VolumeDescentTheorem

/-! All-degree form of Corollary 2.34. Degree zero has no volume
data or measure equation, exactly as mRV[0]=RV[0]. Positive degrees
use the actual definable nonzero forms and essential restrictions. -/

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section2.ConcreteVolumeForms
open IntegrationInACVF.Section2.ConcreteVolumeMorphisms

namespace IntegrationInACVF.Section2.VolumeDescentAllDegrees

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

noncomputable def Form (U : RVFiniteObject (M := M) S k) : Type :=
  match k with
  | 0 => PUnit
  | _+1 => RVForm U

noncomputable def PreservesLift {U V : RVFiniteObject (M := M) S k}
    (ω : Form U) (π : Form V)
    (f : Map (rvLift (rvFiniteEssentialPart U).obj) (rvLift (rvFiniteEssentialPart V).obj)) : Prop := by
  cases k with
  | zero => exact True
  | succ j => exact PreservesOff (essentialForm ω) (essentialForm π) f

noncomputable def IsVolumeIsomorphism {U V : RVFiniteObject (M := M) S k}
    (e : RVFiniteEssentialIso U V) (ω : Form U) (π : Form V) : Prop := by
  cases k with
  | zero => exact True
  | succ j =>
    exact ConcreteVolumeMorphisms.IsVolumeIsomorphism e (essentialForm ω) (essentialForm π)
      (rvEssential_value_nonzero U.obj) (rvEssential_value_nonzero V.obj)

theorem corollary_2_34_all_degrees (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U V : RVFiniteObject (M := M) (C.base : Set M) k}
    (e : RVFiniteEssentialIso U V) (ω : Form U) (π : Form V)
    (f : Map (rvLift (rvFiniteEssentialPart U).obj) (rvLift (rvFiniteEssentialPart V).obj))
    (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift (rvFiniteEssentialPart U).obj,
      ((finiteVolumeProperty (C.base : Set M) k).ι.mapIso e).hom.map.graph p.val.2 (f p).val.2)
    (hMeasure : PreservesLift ω π f) : IsVolumeIsomorphism e ω π := by
  cases k with
  | zero => trivial
  | succ j => exact IntegrationInACVF.Section2.corollary_2_34 hc C e ω π f hf hlabel hMeasure

end IntegrationInACVF.Section2.VolumeDescentAllDegrees
