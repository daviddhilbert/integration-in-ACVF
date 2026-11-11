import IntegrationSection3ACVF.FullGammaControllers
import IntegrationSection3ACVF.RealParameterTuples
import Section3.GammaRVSeparation

/-! Every definable map from one actual nonzero RV value fibre to RV
has finite value image. The full value-cut graph is built from its actual
partial graph; genuine saturation supplies the checked finite-cut argument. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVFunctionValueCuts

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem cut_family_definable (S D : Set M) (g : M → M)
    (hG : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 2)
      (ImaginaryBaseImages.graphOn D g))
    (hOut : ∀ x ∈ D, NonzeroRV (g x)) :
    @RawClosure.Tuple.RelationDefinable M (@CanonicalStructure.normalize M sM) 1 S
      (cutFamily D (fun x => codeValue (g x))) := by
  have hLt := GammaSyntax.lt_definable S (0 : Fin 2) 1
  let C := cutFamily D (fun x => codeValue (g x))
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  let πG : Fin 2 → (Fin 1 ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  let πL : Fin 2 → (Fin 1 ⊕ Fin 1) ⊕ Fin 1 := ![.inr 0,.inl (.inl 0)]
  have heG (z : Fin 1 ⊕ Fin 1 → M) (y : Fin 1 → M) :
      Sum.elim z y ∘ πG = ![z (.inr 0),y 0] := by funext k; fin_cases k <;> rfl
  have heL (z : Fin 1 ⊕ Fin 1 → M) (y : Fin 1 → M) :
      Sum.elim z y ∘ πL = ![y 0,z (.inl 0)] := by funext k; fin_cases k <;> rfl
  have hd : @Set.Definable M S LRV N (Fin 1 ⊕ Fin 1)
      {z | ∃ y : Fin 1 → M, Sum.elim z y ∘ πG ∈ ImaginaryBaseImages.graphOn D g ∧
        Sum.elim z y ∘ πL ∈ {a | GammaSyntax.Proper a ∧ codeValue (a 0) < codeValue (a 1)}} := by
    letI := N
    exact ((hG.preimage_comp πG).inter (hLt.preimage_comp πL)).exists_of_finite
  change @Set.Definable M S LRV N (Fin 1 ⊕ Fin 1) {z | (z ∘ Sum.inl,z (.inr 0)) ∈ C}
  convert hd using 1
  ext z
  simp_rw [heG,heL]
  change (NonzeroRV (z (.inl 0)) ∧ z (.inr 0) ∈ D ∧ codeValue (g (z (.inr 0))) < codeValue (z (.inl 0))) ↔
    ∃ y : Fin 1 → M, (z (.inr 0) ∈ D ∧ y 0 = g (z (.inr 0))) ∧
      GammaSyntax.Proper ![y 0,z (.inl 0)] ∧ codeValue (y 0) < codeValue (z (.inl 0))
  constructor
  · rintro ⟨hβ,hx,hCut⟩
    refine ⟨![g (z (.inr 0))],⟨hx,rfl⟩,?_,hCut⟩
    intro i
    fin_cases i
    · exact hOut _ hx
    · exact hβ
  · rintro ⟨y,⟨hx,hy⟩,hProper,hCut⟩
    rw [hy] at hCut
    exact ⟨hProper 1,hx,hCut⟩

theorem finite_value_image {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (D : Set M) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn D g))
    (hD : D ⊆ {x | iRV x}) (hOut : ∀ x ∈ D, NonzeroRV (g x))
    (γ : Values.Gamma (M := M))
    (hDγ : ∀ t : CanonicalRV.RVSort M, t.val ∈ D → Values.vrv t = γ.val) :
    ((fun x => codeValue (g x)) '' D).Finite := by
  let p := @ParameterPresentation.presentation M sM hM
  have hSpecial : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (@CanonicalStructure.normalize M sM) (Fin 2)
        (ImaginaryBaseImages.graphOn D g) := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryParameters.OverBase.specialize hG
  obtain ⟨E,hE,hRawG⟩ := hSpecial
  let S := B.real ∪ E
  have hSmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall E hE
  have hRawD : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 1)
      {z | z 0 ∈ D} := by
    let π : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0,.inr 0]
    letI := @CanonicalStructure.normalize M sM
    have hd := (hRawG.preimage_comp π).exists_of_finite
    convert hd using 1
    ext z
    change z 0 ∈ D ↔ ∃ y : Fin 1 → M, z 0 ∈ D ∧ y 0 = g (z 0)
    exact ⟨fun hz => ⟨![g (z 0)],hz,rfl⟩,fun ⟨_,hz,_⟩ => hz⟩
  have hDDef : DefinableAt S .rv D := (@definableAt_iff_normalized_raw M sM hM S .rv D).mpr ⟨hRawD,hD⟩
  exact finite_image_of_definable_cuts hs S D hSmallS hDDef γ hDγ
    (fun x => codeValue (g x)) (cut_family_definable S D g hRawG hOut)

end IntegrationInACVF.Section3ACVF.RVFunctionValueCuts
