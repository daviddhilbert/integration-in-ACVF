import IntegrationSection3ACVF.CoordinatePartitions
import IntegrationSection3ACVF.BallEnlargementGeometry

/-! Independent boundary check for Proposition3.24. Definition2.2 calls
VF clopen. If the closed parent is allowed to be VF, the same punctured
whole field is both source and target, and the identity is open-to-open.
This is a counterexample to that literal boundary scope, not a proof of3.24. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.Proposition324WholeFieldBoundary

open GammaRadiusAtomicity PuncturedGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem counterexample (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ d : PuncturedBall M, d.parent = {x | iVF x} ∧ d.body.Nonempty ∧
      PaperBalls.IsClosedBall d.parent ∧ PaperBalls.IsOpenBall d.parent ∧
      d.holes.card = 1 ∧ (∀ H ∈ d.holes, PaperBalls.IsOpenBall H) ∧
      ∃ B : FullBaseAtomicity.Base (M := M), B.real.Finite ∧ B.imaginary = {Sum.inr δ} ∧ FullGammaSyntax.Scalar B {δ} ∧
        FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body id) ∧
        Set.BijOn id d.body d.body ∧ MaximalOpenClasses.OpenToOpen d.body id := by
  classical
  let H := gammaBall (0 : VFType (M := M)) (1 : Values.Gamma (M := M)) true
  have hHBall : IsBall H := BallEnlargementGeometry.gammaBall_isBall 0 1 true
  have hHOpen : PaperBalls.IsOpenBall H := Or.inr ⟨0,1,rfl⟩
  have hProper : H ⊂ {x : M | iVF x} := BallEnlargementGeometry.gammaBall_proper_in_vf δ hδ 0 1 true
  let d : PuncturedBall M := ⟨{x | iVF x},Or.inl rfl,{H},
    fun h hh => (Finset.mem_singleton.mp hh) ▸ hHBall,
    fun h hh => (Finset.mem_singleton.mp hh) ▸ hProper,
    by intro h hh k hk hne; exact (hne ((Finset.mem_singleton.mp hh).trans (Finset.mem_singleton.mp hk).symm)).elim⟩
  obtain ⟨q,hq,hqH⟩ := ParameterizedOpenImages.exists_open_code hHOpen
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨∅,∅⟩
  let B := RealParameterTuples.extend B0 q
  have hHDef : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ H} := by
    have hd := RealParameterTuples.specialize B0 q (OpenImageConfigurations.body_definable B0)
    apply FullBaseAtomicity.OverBase.congr hd
    intro z
    change z 0 ∈ OpenImageConfigurations.body q ↔ z 0 ∈ H
    rw [hqH]
  have hVF : FullBaseAtomicity.OverBase B {z : Fin 1 → M | iVF (z 0)} :=
    FullBaseAtomicity.OverBase.of_real (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
      (@definableAt_sort M sM B.real .vf)).1)
  have hD : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ d.body} := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hVF
      (FullBaseAtomicity.OverBase.compl hHDef))
    intro z
    change (iVF (z 0) ∧ z 0 ∉ H) ↔ (iVF (z 0) ∧ ¬ ∃ h ∈ ({H} : Finset (Set M)), z 0 ∈ h)
    simp only [Finset.mem_singleton,exists_eq_left]
  have hEq : FullBaseAtomicity.OverBase B {z : Fin 2 → M | z 1 = z 0} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact SpecialTransformations.Section3.RawClosure.definable_equal_coordinates B.real 1 0
  have hGraph : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body id) :=
    FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp hD (fun _ => (0 : Fin 2))) hEq
  have hNonempty : d.body.Nonempty := by
    obtain ⟨x,hxVF,hxH⟩ := Set.exists_of_ssubset hProper
    refine ⟨x,hxVF,?_⟩
    rintro ⟨h,hh,hxh⟩
    exact hxH ((Finset.mem_singleton.mp hh) ▸ hxh)
  let C := B.adjoin (Sum.inr δ)
  have hCδ : FullGammaSyntax.Scalar C {δ} := AdjoinGamma.named_scalar δ (Set.mem_insert _ _)
  have hGraphC : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn d.body id) :=
    FullBaseAtomicity.OverBase.mono hGraph Set.Subset.rfl (Set.subset_insert _ _)
  have hImag : C.imaginary = {Sum.inr δ} := by
    change insert (Sum.inr δ) (∅ : Set (ParameterPresentation.Name (M := M))) = {Sum.inr δ}
    ext i
    change (i = Sum.inr δ ∨ False) ↔ i = Sum.inr δ
    exact ⟨fun h => h.resolve_right id,Or.inl⟩
  refine ⟨d,rfl,hNonempty,Or.inl rfl,Or.inl rfl,Finset.card_singleton H,?_,C,?_,hImag,hCδ,hGraphC,?_,?_⟩
  · intro h hh
    exact (Finset.mem_singleton.mp hh) ▸ hHOpen
  · change (∅ ∪ Set.range q).Finite
    exact Set.finite_empty.union (Set.finite_range q)
  · exact ⟨fun _ hx => hx,fun _ _ _ _ he => he,fun y hy => ⟨y,hy,rfl⟩⟩
  · intro D _
    rw [Set.image_id]

end IntegrationInACVF.Section3ACVF.Proposition324WholeFieldBoundary
