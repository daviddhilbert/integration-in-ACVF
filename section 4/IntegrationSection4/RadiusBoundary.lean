import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3ACVF.RealParameterTuples
import IntegrationSection3ACVF.ParameterizedOpenImages
import IntegrationSection3ACVF.MaximalOpenClasses
import IntegrationSection3ACVF.AdjoinGamma

/-! A boundary check for the literal singleton claim in Lemma 4.3.
This uses actual ball point sets and the sequel's actual radius predicate.
It does not adopt a correction to the paper's statement. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section4.RadiusBoundary

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem no_subset_at_smaller_radius (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α < β)
    {D : Set M} (hD : PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M))) :
    ¬ D ⊆ gammaBall a β true := by
  obtain ⟨c, strict, hc⟩ := BallEnlargementGeometry.ordinary_presentation α hD
  rw [hc]
  intro hs
  exact (not_le_of_gt hαβ)
    (BallEnlargementGeometry.gamma_radius_le_of_subset δ hδ c a β α strict true hs)

/-- The displayed radius set in 4.3, specialized to the identity map on E.
Using the actual `HasRadius` predicate also includes the paper's singleton
and whole-field conventions. -/
def identityRadiusSet (E : Set M) (α : Values.Gamma (M := M)) :
    Set (PaperBalls.Radius (M := M)) :=
  {r | ∃ D : Set M, PaperBalls.IsOpenBall D ∧ D ⊆ E ∧
    PaperBalls.HasRadius D r ∧
    PaperBalls.HasRadius D (↑α.val : PaperBalls.Radius (M := M))}

theorem identityRadiusSet_empty (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α < β)
    (E : Set M) (hE : E ⊆ gammaBall a β true) : identityRadiusSet E α = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨D, _, hDE, _, hDα⟩
  exact no_subset_at_smaller_radius δ hδ a α β hαβ hDα (hDE.trans hE)

theorem identityRadiusSet_not_singleton (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α < β)
    (E : Set M) (hE : E ⊆ gammaBall a β true) (r : PaperBalls.Radius (M := M)) :
    identityRadiusSet E α ≠ {r} := by
  rw [identityRadiusSet_empty δ hδ a α β hαβ E hE]
  exact Set.empty_ne_singleton r

/-- A definable identity on an ordinary open ball, with a finite real base
and an originally named nontrivial Gamma value. At alpha=1 every possible
inverse piece has an empty requested-radius set. No special preparation can
turn that empty set into the literal singleton demanded by printed 4.3. -/
theorem identity_counterexample (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ A : Set M, A.Nonempty ∧ PaperBalls.IsOpenBall A ∧
      ∃ B : FullBaseAtomicity.Base (M := M), B.real.Finite ∧
        B.imaginary = {Sum.inr δ} ∧ FullGammaSyntax.Scalar B {δ} ∧
        FullGammaSyntax.Scalar B {(1 : Values.Gamma (M := M))} ∧
        FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A id) ∧
        Set.BijOn id A A ∧ MaximalOpenClasses.OpenToOpen A id ∧
        ∀ E : Set M, E ⊆ A → identityRadiusSet E 1 = ∅ := by
  classical
  let A := gammaBall (0 : VFType (M := M)) δ true
  have hOpen : PaperBalls.IsOpenBall A := Or.inr ⟨0, δ, rfl⟩
  obtain ⟨q, _, hqA⟩ := ParameterizedOpenImages.exists_open_code hOpen
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨∅, ∅⟩
  let B := RealParameterTuples.extend B0 q
  have hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A} := by
    have hd := RealParameterTuples.specialize B0 q (OpenImageConfigurations.body_definable B0)
    apply FullBaseAtomicity.OverBase.congr hd
    intro z
    change z 0 ∈ OpenImageConfigurations.body q ↔ z 0 ∈ A
    rw [hqA]
  have hEq : FullBaseAtomicity.OverBase B {z : Fin 2 → M | z 1 = z 0} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact SpecialTransformations.Section3.RawClosure.definable_equal_coordinates B.real 1 0
  have hGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A id) :=
    FullBaseAtomicity.OverBase.inter
      (FullBaseAtomicity.OverBase.preimage_comp hA (fun _ => (0 : Fin 2))) hEq
  let C := B.adjoin (Sum.inr δ)
  have hCδ : FullGammaSyntax.Scalar C {δ} := AdjoinGamma.named_scalar δ (Set.mem_insert _ _)
  have hGraphC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn A id) :=
    FullBaseAtomicity.OverBase.mono hGraph Set.Subset.rfl (Set.subset_insert _ _)
  have hImag : C.imaginary = {Sum.inr δ} := by
    change insert (Sum.inr δ) (∅ : Set (ParameterPresentation.Name (M := M))) = {Sum.inr δ}
    ext i
    change (i = Sum.inr δ ∨ False) ↔ i = Sum.inr δ
    exact ⟨fun h => h.resolve_right id, Or.inl⟩
  refine ⟨A, ⟨(0 : VFType (M := M)).val, ?_⟩, hOpen, C, ?_, hImag,
    hCδ, FullGammaSyntax.one_definable C, hGraphC, ?_, ?_, ?_⟩
  · exact BallEnlargementGeometry.gammaBall_centre_mem 0 δ true
  · change (∅ ∪ Set.range q).Finite
    exact Set.finite_empty.union (Set.finite_range q)
  · exact ⟨fun _ hx => hx, fun _ _ _ _ he => he, fun y hy => ⟨y, hy, rfl⟩⟩
  · intro D _
    rw [Set.image_id]
  · intro E hE
    exact identityRadiusSet_empty δ hδ 0 1 δ hδ E hE

end IntegrationInACVF.Section4.RadiusBoundary
