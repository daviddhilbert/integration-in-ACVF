import Integration7.NativeRelativeTranslationVolumes
import IntegrationSection5.CoordinateFibreMaps

/-! A definable centre read from another VF coordinate and the retained
RV labels is independent of the active coordinate of a translation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def otherCoordinateCentreMap (A : DefSet (M := M) S n a) (D : DefSet (M := M) S 1 a)
    (j : Fin n) (c : Map D (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hD : ∀ p : A, (coordinateProjectMap j A p).val ∈ carrier D) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.comp c (mapIntoSubset (coordinateProjectMap j A) D hD)

theorem other_coordinate_centre_value (A : DefSet (M := M) S n a) (D : DefSet (M := M) S 1 a)
    (j : Fin n) (c : Map D (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hD : ∀ p : A, (coordinateProjectMap j A p).val ∈ carrier D) (p : A) :
    (otherCoordinateCentreMap A D j c hD p).val = (c ⟨coordinateProject j p.val,hD p⟩).val := rfl

theorem other_coordinate_centre_independent (A : DefSet (M := M) S n a) (D : DefSet (M := M) S 1 a)
    (i j : Fin n) (hij : j ≠ i)
    (c : Map D (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hD : ∀ p : A, (coordinateProjectMap j A p).val ∈ carrier D)
    (p q : A) (he : erase i p.val = erase i q.val) :
    (otherCoordinateCentreMap A D j c hD p).val 0 = (otherCoordinateCentreMap A D j c hD q).val 0 := by
  have hv : p.val.1 j = q.val.1 j := by
    have h := congrArg (fun z => z.1 j) he
    simpa only [erase,replace,Function.update_of_ne hij] using h
  have hr0 := congrArg (fun z : Point (M := M) n a => z.2) he
  have hr : p.val.2 = q.val.2 := hr0
  have hpq : (⟨coordinateProject j p.val,hD p⟩ : D) = ⟨coordinateProject j q.val,hD q⟩ := by
    apply Subtype.ext
    exact Prod.ext (funext fun _ => hv) hr
  exact congrArg (fun z : D => (c z).val 0) hpq

end IntegrationInACVF.Section7
