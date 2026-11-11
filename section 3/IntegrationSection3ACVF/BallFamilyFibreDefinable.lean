import IntegrationSection3ACVF.FullBallCoset

/-! A same-base full ball-indexed relation has its fibre definable after
adjoining precisely that actual ball name. No real code is named. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.BallFamilyFibreDefinable

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem fibre_definable (B : FullBaseAtomicity.Base (M := M))
    (P : BallImaginaries.Ball M → Set M) (hP : FullBaseAtomicity.Relation B P)
    (i : BallImaginaries.Ball M) :
    FullBaseAtomicity.OverBase (B.adjoin (Sum.inl i)) {z : Fin 1 → M | z 0 ∈ P i} := by
  let B' := B.adjoin (Sum.inl i)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hp := ParameterPresentation.presentation_definable (M := M) B'.real
  have hIndex : FullBaseAtomicity.Family B' {i} := by
    have hn : FullBaseAtomicity.OverBase B' (p.pullback {Sum.inl i}) := by
      letI := @CanonicalStructure.normalize M sM
      exact ImaginaryParameters.OverBase.named_singleton (B := B') hp (Set.mem_insert _ _)
    have h := AdjoinBall.restrict_family B' {Sum.inl i} hn
    convert h using 1
    ext D
    simp only [Set.mem_singleton_iff,Set.mem_setOf_eq,Sum.inl.injEq]
  have hP' : FullBaseAtomicity.Relation B' P :=
    FullBaseAtomicity.OverBase.mono hP Set.Subset.rfl (Set.subset_insert _ _)
  have hd : FullBaseAtomicity.OverBase B'
      {z : Fin 1 → M | ∃ D ∈ ({i} : Set (BallImaginaries.Ball M)), z 0 ∈ P D} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryBaseFamilies.Relation.range (ImaginaryBaseFamilies.Relation.restrict
      (p := p) (q := q) hp.1 hIndex hP')
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  simp only [Set.mem_setOf_eq,Set.mem_singleton_iff,exists_eq_left]

end IntegrationInACVF.Section3ACVF.BallFamilyFibreDefinable
