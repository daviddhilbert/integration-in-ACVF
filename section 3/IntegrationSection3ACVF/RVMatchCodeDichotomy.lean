import IntegrationSection3ACVF.RVMatchCodeRelations

/-! Every proper code-pair splits its entire source value fibre into a
finite or cofinite matched row. Empty source value rows are handled
explicitly, so the later uniform finite bound has its full parameter domain. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVMatchCodeDichotomy

open RVMatchCodeRelations FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_side (B : FullBaseAtomicity.Base (M := M))
    (I : Set (Values.Gamma (M := M))) (g : M → M)
    (hG : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g))
    (a : Fin 2 → M) (ha : GammaSyntax.Proper a) :
    (matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite ∨
      (sourceRow (Values.gammaPullback I) a \ matchRow (ImaginaryBaseImages.graphOn (Values.gammaPullback I) g) a).Finite := by
  let U := Values.gammaPullback I
  let R := matchRow (ImaginaryBaseImages.graphOn U g) a
  let γ := codeValue (a 0)
  have hRSub : R ⊆ sourceRow U a := matchRow_subset_source U g a
  by_cases hI : γ ∈ I
  · have hSource : sourceRow U a = fibre γ := sourceRow_eq I a ha hI
    have hRFibre : R ⊆ fibre γ := fun x hx => (Set.ext_iff.mp hSource x).mp (hRSub hx)
    have hDef : FullBaseAtomicity.OverBase (RealParameterTuples.extend B a) {z : Fin 1 → M | z 0 ∈ R} :=
      matchRow_definable B hG a
    have hSide := FullRVValueFibres.finite_or_cofinite (RealParameterTuples.extend B a) R hDef
      (fun x hx => (subset_nonzero γ (hRFibre hx)).1) γ
    have he : R ∩ fibre γ = R := Set.inter_eq_left.mpr hRFibre
    rw [he] at hSide
    change R.Finite ∨ (sourceRow U a \ R).Finite
    rwa [hSource]
  · have hSource : sourceRow U a = ∅ := sourceRow_empty I a hI
    have hREmpty : R ⊆ ∅ := hSource ▸ hRSub
    exact Or.inl (Set.finite_empty.subset hREmpty)

end IntegrationInACVF.Section3ACVF.RVMatchCodeDichotomy
