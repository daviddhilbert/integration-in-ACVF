import IntegrationSection3ACVF.RVMatchCodeRelations
import IntegrationSection3ACVF.RVValueMatching

/-! Uniform code rows agree exactly with actual dominant value rows and
with the already proved semantic Gamma matching. Every proper label code
is retained in these equivalences. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVMatchRowSemantics

open RVMatchCodeRelations FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nonempty_labels (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hMap : (Values.gammaPullback I).MapsTo g (Values.gammaPullback J)) (a : Fin 2 → M)
    (hRow : (matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Nonempty) :
    codeValue (a 0) ∈ I ∧ codeValue (a 1) ∈ J := by
  obtain ⟨x,hx⟩ := hRow
  have h := (matchRow_iff (Values.gammaPullback I) g a x).mp hx
  have hI := ((GammaSyntax.mem_gammaPullback_iff I x).mp h.1).2
  have hJ := ((GammaSyntax.mem_gammaPullback_iff J (g x)).mp (hMap h.1)).2
  constructor
  · rw [h.2.1.2.2]
    exact hI
  · rw [h.2.2.2.2]
    exact hJ

theorem matchRow_eq (I : Set (Values.Gamma (M := M))) (g : M → M)
    (a : Fin 2 → M) (ha : GammaSyntax.Proper a) (hI : codeValue (a 0) ∈ I)
    (hOut : ∀ x ∈ fibre (codeValue (a 0)), NonzeroRV (g x)) :
    matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a =
      CofiniteRVRows.row g (codeValue (a 0)) (codeValue (a 1)) := by
  ext x
  rw [matchRow_iff]
  constructor
  · rintro ⟨_,hSource,hTarget⟩
    exact ⟨(mem_fibre_code _ x hSource.2.1).mpr hSource.2.2.symm,hTarget.2.2.symm⟩
  · rintro ⟨hx,hVal⟩
    have hx0 := subset_nonzero _ hx
    have hEq := (mem_fibre_code _ x hx0).mp hx
    have hxU : x ∈ Values.gammaPullback I := (GammaSyntax.mem_gammaPullback_iff I x).mpr
      ⟨hx0,by rw [hEq]; exact hI⟩
    exact ⟨hxU,⟨ha 0,hx0,hEq.symm⟩,⟨ha 1,hOut x hx,hVal.symm⟩⟩

theorem cofinite_matches_iff (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (I J : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (hbij : Set.BijOn g (Values.gammaPullback I) (Values.gammaPullback J))
    (a : Fin 2 → M) (ha : GammaSyntax.Proper a)
    (hI : codeValue (a 0) ∈ I) (hJ : codeValue (a 1) ∈ J) :
    (fibre (codeValue (a 0)) \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ↔
      CofiniteClassMatching.Matches (RVValueMatching.classes I) (RVValueMatching.classes J) g
        ⟨codeValue (a 0),hI⟩ ⟨codeValue (a 1),hJ⟩ := by
  let γ : I := ⟨codeValue (a 0),hI⟩
  let η : J := ⟨codeValue (a 1),hJ⟩
  let C := B.adjoin (Sum.inr γ.val)
  have hSub := RVValueMatching.class_subset I γ
  have hGγ : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (fibre γ.val) g) :=
    FullRVClassRestriction.graph_definable B (Values.gammaPullback I) g hG γ.val hSub
  have hOut (x : M) (hx : x ∈ fibre γ.val) : NonzeroRV (g x) :=
    ((GammaSyntax.mem_gammaPullback_iff J (g x)).mp (hbij.1 (hSub hx))).1
  have heR := matchRow_eq I g a ha hI hOut
  have heL : fibre γ.val \ g ⁻¹' fibre η.val = fibre γ.val \ CofiniteRVRows.row g γ.val η.val := by
    ext x
    constructor
    · rintro ⟨hx,hxBad⟩
      exact ⟨hx,fun hRow => hxBad ((mem_fibre_code η.val (g x) (hOut x hx)).mpr hRow.2)⟩
    · rintro ⟨hx,hxBad⟩
      exact ⟨hx,fun hTarget => hxBad ⟨hx,(mem_fibre_code η.val (g x) (hOut x hx)).mp hTarget⟩⟩
  constructor
  · intro hCo
    rw [heR] at hCo
    exact ⟨heL.symm ▸ hCo,CofiniteRVRows.cofinite_target h00 C g γ.val η.val hGγ hOut
      (hbij.2.1.mono hSub) hCo⟩
  · intro hMatch
    have hCo : (fibre γ.val \ CofiniteRVRows.row g γ.val η.val).Finite := heL ▸ hMatch.1
    rwa [← heR] at hCo

end IntegrationInACVF.Section3ACVF.RVMatchRowSemantics
