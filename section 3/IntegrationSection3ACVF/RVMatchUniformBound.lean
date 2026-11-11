import IntegrationSection3ACVF.RVMatchCodeDichotomy
import IntegrationSection3ACVF.FiniteBaseRealPresentation
import Section3.RVFibreGeometry

/-! Genuine uniform bounds for the finite sides of all value-code match
rows. Original imaginary support is finite only internally; all actual
rows retain their original full parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVMatchUniformBound

open RVMatchCodeRelations

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (I : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g)) :
    ∃ N : ℕ, ∀ a : Fin 2 → M, GammaSyntax.Proper a →
      ((matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ∧
        (matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).ncard ≤ N) ∨
      ((sourceRow (Values.gammaPullback I) a \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ∧
        (sourceRow (Values.gammaPullback I) a \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).ncard ≤ N) := by
  classical
  let U := Values.gammaPullback I
  let H := ImaginaryBaseImages.graphOn U g
  obtain ⟨F,hF,hData⟩ := hG
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨B.real,(F : Set (ParameterPresentation.Name (M := M)))⟩
  have hG0 : FullBaseAtomicity.OverBase B0 H := ⟨F,fun _ hi => hi,hData⟩
  have hU0 : FullBaseAtomicity.OverBase B0 {z : Fin 1 → M | z 0 ∈ U} := by
    have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.preimage_comp hG0
      (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
    apply FullBaseAtomicity.OverBase.congr hd
    intro z
    change (∃ y : Fin 1 → M, z 0 ∈ U ∧ y 0 = g (z 0)) ↔ z 0 ∈ U
    exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => ⟨![g (z 0)],hz,rfl⟩⟩
  have hR0 := matchCodes_definable B0 hG0
  have hS0 := sourceCodes_definable B0 U hU0
  have hQ0 := FullBaseAtomicity.OverBase.inter hS0 (FullBaseAtomicity.OverBase.compl hR0)
  have hP0 : FullBaseAtomicity.OverBase B0 {a : Fin 2 → M | GammaSyntax.Proper a} :=
    FullGammaSyntax.proper_definable B0
  let P : Set (Fin 2 → M) := {a | GammaSyntax.Proper a}
  let R : Set ((Fin 2 → M) × M) := {p | p.2 ∈ matchRow H p.1}
  let Q : Set ((Fin 2 → M) × M) := {p | p.2 ∈ sourceRow U p.1 \ matchRow H p.1}
  obtain ⟨E,hE,hPresentation⟩ := FiniteBaseRealPresentation.exists_common_codes B0 F.finite_toSet
  let S := B.real ∪ E
  have hSmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall E hE
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hPRaw : @Set.Definable M S LRV N (Fin 2) P := hPresentation (Fin 2) P hP0
  have hRRaw : @RawClosure.Tuple.RelationDefinable M N 2 S R := by
    have hd := hPresentation (Fin 2 ⊕ Fin 1) (matchCodes H) hR0
    change @Set.Definable M S LRV N (Fin 2 ⊕ Fin 1) {z | (z ∘ Sum.inl,z (.inr 0)) ∈ R}
    convert hd using 1
    ext z
    have he : Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] = z := by
      funext k
      cases k with
      | inl k => rfl
      | inr k => fin_cases k; rfl
    change (Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] ∈ matchCodes H) ↔ z ∈ matchCodes H
    rw [he]
  have hQRaw : @RawClosure.Tuple.RelationDefinable M N 2 S Q := by
    have hd := hPresentation (Fin 2 ⊕ Fin 1) (sourceCodes U ∩ (matchCodes H)ᶜ) hQ0
    change @Set.Definable M S LRV N (Fin 2 ⊕ Fin 1) {z | (z ∘ Sum.inl,z (.inr 0)) ∈ Q}
    convert hd using 1
    ext z
    have he : Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] = z := by
      funext k
      cases k with
      | inl k => rfl
      | inr k => fin_cases k; rfl
    change (Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] ∈ sourceCodes U ∧
      Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] ∉ matchCodes H) ↔ (z ∈ sourceCodes U ∧ z ∉ matchCodes H)
    rw [he]
  have hSide (a : Fin 2 → M) (ha : a ∈ P) : {x | (a,x) ∈ R}.Finite ∨ {x | (a,x) ∈ Q}.Finite :=
    RVMatchCodeDichotomy.finite_side B0 I g hG0 a ha
  exact @RawClosure.Tuple.uniform_finite_side M N 2 κ hs.normalize S hSmallS P hPRaw R Q hRRaw hQRaw hSide

end IntegrationInACVF.Section3ACVF.RVMatchUniformBound
