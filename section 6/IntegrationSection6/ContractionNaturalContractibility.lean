import IntegrationSection6.FiniteContractionLabels
import IntegrationSection6.TypedRelabeling

/-! A VF-preserving contraction with a contractible final RV map has a
mutually contractible natural lift. Its inverse retains the original labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def typedContractionNaturalMap (C : StandardContraction U σ) : Map U (typedLift C.normalizedObject) :=
  Map.comp (rawLiftToTypedMap C.normalizedObject) C.normalizedNaturalLiftMap

theorem typedContractionNaturalMap_bijective (C : StandardContraction U σ) :
    Function.Bijective (typedContractionNaturalMap C) :=
  (rawLiftToTypedMap_bijective C.normalizedObject).comp C.normalizedNaturalLiftMap_bijective

theorem typedContractionNaturalMap_vf (C : StandardContraction U σ)
    (hVF : ∀ u : U, (C.naturalMap u).val.1 = u.val.1) (u : U) :
    (typedContractionNaturalMap C u).val.1 = u.val.1 := hVF u

theorem typedContractionNaturalMap_contractible (C : StandardContraction U σ)
    (hVF : ∀ u : U, (C.naturalMap u).val.1 = u.val.1) (hc : Contractible C.toMap) :
    Contractible (typedContractionNaturalMap C) := by
  intro u v huv
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,?_⟩
  · intro j
    exact (congrArg (@rv M sM hM) (congrFun (hVF u) j)).trans
      (((sameRV_iff _ _).mp huv).1 j |>.trans (congrArg (@rv M sM hM) (congrFun (hVF v) j)).symm)
  · have he : C.toMap u = C.toMap v := Subtype.ext
      (Prod.ext (funext fun j => Fin.elim0 j) ((sameRV_iff _ _).mp (hc u v huv)).2)
    change (C.normalizedNaturalLiftMap u).val.2 = (C.normalizedNaturalLiftMap v).val.2
    rw [C.normalizedNaturalLiftMap_square,C.normalizedNaturalLiftMap_square]
    exact congrArg (fun w : C.target =>
      (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex (Map.toImage (rawLabelMap C.target) w)).val) he

theorem typedContractionNaturalMap_inverse_contractible (C : StandardContraction U σ)
    (hVF : ∀ u : U, (C.naturalMap u).val.1 = u.val.1) :
    Contractible (Map.inverse (typedContractionNaturalMap C) (typedContractionNaturalMap_bijective C)) := by
  let f := typedContractionNaturalMap C
  let hf := typedContractionNaturalMap_bijective C
  intro u v huv
  let x := Map.inverse f hf u
  let y := Map.inverse f hf v
  have hx : f x = u := Map.apply_inverse f hf u
  have hy : f y = v := Map.apply_inverse f hf v
  have hxp : (f x).val.1 = x.val.1 := hVF x
  have hyp : (f y).val.1 = y.val.1 := hVF y
  have hr := (sameRV_iff _ _).mp huv
  apply (sameRV_iff _ _).mpr
  constructor
  · intro j
    have hx' := congrArg (fun z : typedLift C.normalizedObject => z.val.1 j) hx
    have hy' := congrArg (fun z : typedLift C.normalizedObject => z.val.1 j) hy
    exact (congrArg (@rv M sM hM) ((congrFun hxp j).symm.trans hx')).trans
      ((hr.1 j).trans (congrArg (@rv M sM hM) ((congrFun hyp j).symm.trans hy')).symm)
  · funext j
    have hOld (a : U) : (f a).val.2 (FiniteRV.contractionOldLabelIndex C j) = a.val.2 j :=
      (congrArg (fun r => r (FiniteRV.contractionOldLabelIndex C j)) (C.normalizedNaturalLiftMap_square a)).trans
        (FiniteRV.contraction_oldLabels C a j)
    exact (hOld x).symm.trans ((congrArg (fun z : typedLift C.normalizedObject =>
      z.val.2 (FiniteRV.contractionOldLabelIndex C j)) hx).trans
        ((congrFun hr.2 (FiniteRV.contractionOldLabelIndex C j)).trans
          ((congrArg (fun z : typedLift C.normalizedObject => z.val.2 (FiniteRV.contractionOldLabelIndex C j)) hy).symm.trans (hOld y))))

end IntegrationInACVF.Section6
