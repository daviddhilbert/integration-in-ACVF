import IntegrationSection3ACVF.ParameterPresentation

/-! Parametric ball atomicity with genuine Gamma and ball names in the base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.FullBaseAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev Base := ImaginaryParameters.Base M (ParameterPresentation.Name (M := M))

abbrev OverBase (B : Base (M := M)) {α : Type} (A : Set (α → M)) : Prop :=
  @ImaginaryParameters.OverBase LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5)
    (@ParameterPresentation.presentation M sM hM) B α A

abbrev Family (B : Base (M := M)) (T : Set (BallImaginaries.Ball M)) : Prop :=
  OverBase B ((@BallPresentation.presentation M sM hM).pullback T)

abbrev Relation (B : Base (M := M)) (C : BallImaginaries.Ball M → Set M) : Prop :=
  OverBase B ((@BallPresentation.presentation M sM hM).relationPullback C)

abbrev Algebraic (B : Base (M := M)) (i : BallImaginaries.Ball M) : Prop :=
  @ImaginaryBaseFamilies.Algebraic LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5) (BallImaginaries.Ball M) (Fin 4)
    (@ParameterPresentation.presentation M sM hM) B (@BallPresentation.presentation M sM hM) i

abbrev AtomicWith (B : Base (M := M)) (i : BallImaginaries.Ball M) (A : Set M) : Prop :=
  @ImaginaryBaseFamilies.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
    (ParameterPresentation.Name (M := M)) (Fin 5) (BallImaginaries.Ball M) (Fin 4)
    (@ParameterPresentation.presentation M sM hM) B (@BallPresentation.presentation M sM hM) i A

/-- Lemma 3.2 with arbitrary additional genuine Gamma and ball names.
All graphs and tests use full invariant preimages over the same base. -/
theorem lemma_3_2 (B : Base (M := M)) (T : Set (BallImaginaries.Ball M))
    (f : BallImaginaries.Ball M → BallImaginaries.Ball M)
    (hT : Family B T)
    (hf : OverBase B ((@BallPresentation.presentation M sM hM).functionPullback T f))
    (hdis : T.Pairwise fun i j => Disjoint (BallImaginaries.underlying (f i))
      (BallImaginaries.underlying (f j)))
    {i : BallImaginaries.Ball M} (hi : i ∈ T) (hna : ¬ Algebraic B (f i)) :
    AtomicWith B i (BallImaginaries.underlying (f i)) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let C : BallImaginaries.Ball M → Set M :=
    fun j => {x | j ∈ T ∧ x ∈ BallImaginaries.underlying (f j)}
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hC : Relation B C := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.comp_on hp (ImaginaryParameters.OverBase.of_real hm) hf
  have hc (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      C j = BallImaginaries.underlying (f j) := by
    ext x
    exact and_iff_right hj
  have hb : ∀ j ∈ T, C j ∈ BallPresentation.valuationBalls v := by
    intro j hj
    rw [hc j hj]
    exact BallPresentation.underlying_valuationBall v hv (f j)
  have hd : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hne
    rw [hc j hj,hc k hk]
    exact hdis hj hk hne
  have hl := BallPresentation.valuationBalls_laminar v
  have hcm (Q : Set M) := BallPresentation.normalized_cMinimalOn_valuationBalls Q v hv
  have hei := hc i hi
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  have h := ImaginaryBaseFamilies.parametric_atomic_of_output hp hq hl hcm
    (fun _ hb => hb.1) hT hC hb hd hf hi hna
  change ImaginaryBaseFamilies.AtomicWith (L := LRV) p B q i (C i) at h
  rw [hei] at h
  exact h

end IntegrationInACVF.Section3ACVF.FullBaseAtomicity
