import IntegrationSection3ACVF.RealParameterTuples
import IntegrationSection3.ImaginaryTupleDefinability
import IntegrationSection3.CodeSupportHull
import Section3.GammaBaseTools

/-! Promote finite named real labels into free variables over the full
original interpreted base. Universal code hulls restore invariance at
every label tuple; no arbitrary representative becomes a parameter. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RealParameterPromotion

variable {M α τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem promote [Finite α] (B : FullBaseAtomicity.Base (M := M)) {n : ℕ} (a : Fin n → M)
    {D : Set (α → M)} (hD : FullBaseAtomicity.OverBase (RealParameterTuples.extend B a) D) :
    ∃ R : Set (Fin n ⊕ α → M), FullBaseAtomicity.OverBase B R ∧
      {x : α → M | Sum.elim a x ∈ R} = D := by
  classical
  obtain ⟨F,hF,Q,hQ,hQD⟩ := hD
  let p := @ParameterPresentation.presentation M sM hM
  let q := ImaginaryParameters.tuplePresentation p F
  have hp := ParameterPresentation.presentation_definable (M := M) B.real
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  obtain ⟨W,hW,hWa⟩ := @SpecialTransformations.ModelTheory.promote_definable_tuple_fibre
    LRV M N B.real n ((F × Fin 5) ⊕ α) a (ImaginaryParameters.vectorPullback q Q) hQ
  let R0 : Set (Fin n ⊕ ((F × Fin 5) ⊕ α) → M) :=
    {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ W}
  let H := CodeSupportHull.hull q R0
  have hAt (c : q.codes) (x : α → M) :
      Sum.elim a (Sum.elim c.val x) ∈ R0 ↔ x ∈ Q (q.decode c) := by
    have he := Set.ext_iff.mp hWa (Sum.elim c.val x)
    have hm : Sum.elim c.val x ∈ ImaginaryParameters.vectorPullback q Q ↔ x ∈ Q (q.decode c) :=
      ⟨fun ⟨_,hx⟩ => hx,fun hx => ⟨c.property,hx⟩⟩
    change (a,Sum.elim c.val x) ∈ W ↔ _
    exact he.trans hm
  have hHull : @Set.Definable M B.real LRV N ((F × Fin 5) ⊕ (Fin n ⊕ α))
      (ImaginaryParameters.vectorPullback q H) := by
    letI := N
    have hq := ImaginaryTupleDefinability.isDefinable (p := p) (θ := F) hp
    exact CodeSupportHull.definable hq hW
  refine ⟨H (Subtype.val : F → ParameterPresentation.Name (M := M)),⟨F,hF,H,hHull,rfl⟩,?_⟩
  ext x
  exact (CodeSupportHull.specializes q R0 Q a hAt (Subtype.val : F → ParameterPresentation.Name (M := M)) x).trans
    (Set.ext_iff.mp hQD x)

theorem promote_finite [Finite α] [Finite τ] (B : FullBaseAtomicity.Base (M := M)) (a : τ → M)
    {D : Set (α → M)} (hD : FullBaseAtomicity.OverBase (RealParameterTuples.extend B a) D) :
    ∃ R : Set (τ ⊕ α → M), FullBaseAtomicity.OverBase B R ∧
      {x : α → M | Sum.elim a x ∈ R} = D := by
  classical
  letI := Fintype.ofFinite τ
  let e := Fintype.equivFin τ
  let b : Fin (Fintype.card τ) → M := a ∘ e.symm
  have hRange : Set.range b = Set.range a := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e.symm i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨e i,by simp [b]⟩
  have hD' : FullBaseAtomicity.OverBase (RealParameterTuples.extend B b) D := by
    change @FullBaseAtomicity.OverBase M sM hM ⟨B.real ∪ Set.range b,B.imaginary⟩ α D
    rw [hRange]
    exact hD
  obtain ⟨R,hR,hRD⟩ := promote B b hD'
  let π : Fin (Fintype.card τ) ⊕ α → τ ⊕ α := Sum.map e.symm id
  let G := (fun z : τ ⊕ α → M => z ∘ π) ⁻¹' R
  refine ⟨G,FullBaseAtomicity.OverBase.preimage_comp hR π,?_⟩
  ext x
  have he : Sum.elim a x ∘ π = Sum.elim b x := by
    funext i
    cases i <;> rfl
  change (Sum.elim a x ∘ π ∈ R) ↔ x ∈ D
  rw [he]
  exact Set.ext_iff.mp hRD x

end IntegrationInACVF.Section3ACVF.RealParameterPromotion
