import IntegrationSection5.RelativeSpecialBoundary
import IntegrationSection5.VerticalMeanMap
import IntegrationSection5.HeadContractionGeometry

/-! Genuine fibre-focus and coordinate-canonical steps with the precise
boundaries needed for iteration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

theorem specialRelativeBoundary_of_fibre_focus (f : Map A (PresentedSet.univ (pointSpace n m) S))
    (hi : UnaryRelative (Map.toImage f) i)
    (F : ∀ u : Fin n → VF (M := M), Focus (coordinateFibre A i u) 0 k)
    (hF : ∀ u (p : coordinateFibre A i u), coordinateInsert i u ((F u).toFocusGeometry.eta p.val) =
      (f ⟨coordinateInsert i u p.val,p.property⟩).val)
    (previous : Option Bool) (hp : previous ≠ some true) :
    SpecialRelativeBoundary (Map.toImage f) i previous (some true) := by
  refine ⟨hi,?_⟩
  intro u
  have hEq : (F u).etaImage = coordinateFibre (Map.image f) i u := by
    cases hX : (F u).etaImage with
    | mk X hXdef =>
      cases hY : coordinateFibre (Map.image f) i u with
      | mk Y hYdef =>
        have h : X = Y := by simpa only [hX,hY] using fibreFocus_map_image_carrier f hi F hF u
        subst Y
        rfl
  refine ⟨specialCastTarget (SpecialBijection.centripetal (F u)) hEq,?_,?_,?_⟩
  · rw [specialCastTarget_alternating]
    exact ⟨hp,trivial⟩
  · rw [specialCastTarget_lastKind]
    rfl
  · intro p
    apply Subtype.ext
    apply coordinateInsert_injective i u
    rw [specialCastTarget_val,coordinateFibreMap_insert]
    exact hF u p

theorem specialRelative_headSaturated {a b : ℕ} {X : DefSet (M := M) S (n+1) a}
    {Y : DefSet (M := M) S (n+1) b} {f : Map X Y} (hf : SpecialRelative f 0)
    (hX : HeadSaturated (carrier X)) : HeadSaturated (carrier Y) := by
  apply (headSaturated_iff_coordinateFibre Y).mpr
  intro u
  obtain ⟨hi,hT⟩ := hf
  obtain ⟨T,_⟩ := hT u
  exact T.preserves_pullback ((headSaturated_iff_coordinateFibre X).mp hX u)

theorem coordinateCanonical_tagged (A : DefSet (M := M) S n m) (i : Fin n) :
    Tagged (carrier (coordinateCanonicalImage A i)) i (Fin.castAdd m 0) := by
  rintro _ ⟨a,rfl⟩
  rfl

theorem verticalMeanMap_specialRelativeBoundary {A : DefSet (M := M) S (n+1) m}
    (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hTag : Tagged (carrier A) 0 k) :
    SpecialRelativeBoundary (Map.toImage (verticalMeanMap R h00 d hd)) 0 (some false) (some true) := by
  apply specialRelativeBoundary_of_fibre_focus (verticalMeanMap R h00 d hd)
    (verticalMeanMap_unaryRelative R h00 d hd) (verticalMeanFibreFocus R h00 d hd hTag)
    (fun u p => coordinateInsert_verticalMeanEta R h00 d hd hTag u p.val) (some false)
  decide

def verticalMeanStepTarget {A : DefSet (M := M) S (n+1) m}
    (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d) :
    DefSet (M := M) S (n+1) (1+m) :=
  coordinateCanonicalImage (Map.image (verticalMeanMap R h00 d hd)) 0

def verticalMeanStepMap {A : DefSet (M := M) S (n+1) m}
    (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d) :
    Map A (verticalMeanStepTarget R h00 d hd) :=
  Map.comp (coordinateCanonicalBijection (Map.image (verticalMeanMap R h00 d hd)) 0)
    (Map.toImage (verticalMeanMap R h00 d hd))

theorem verticalMeanStep_boundary {A : DefSet (M := M) S (n+1) m}
    (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hTag : Tagged (carrier A) 0 k) :
    SpecialRelativeBoundary (verticalMeanStepMap R h00 d hd) 0 (some false) (some false) :=
  specialRelativeBoundary_comp _ _ 0 (verticalMeanMap_specialRelativeBoundary R h00 d hd hTag)
    (coordinateCanonical_specialRelativeBoundary _ 0 (some true) (by decide))

theorem verticalMeanStep_headSaturated {A : DefSet (M := M) S (n+1) m}
    (R : VerticalRootFamily A) (h00 : M ⊨ Axioms.ACVF00) (d : ℕ) (hd : R.Bound d)
    {k : Fin m} (hTag : Tagged (carrier A) 0 k) (hA : HeadSaturated (carrier A)) :
    HeadSaturated (carrier (verticalMeanStepTarget R h00 d hd)) :=
  specialRelative_headSaturated (specialRelativeBoundary_forget (verticalMeanStep_boundary R h00 d hd hTag)) hA

end IntegrationInACVF.Section5
