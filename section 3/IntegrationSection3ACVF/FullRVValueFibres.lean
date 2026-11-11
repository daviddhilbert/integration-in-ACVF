import IntegrationSection3ACVF.FullGammaControllers
import Section3.GammaRVSeparation

/-! Actual raw RV value fibres: exact quotient membership, disjointness,
infinitude and finite/cofinite traces over the full original base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fibre (γ : Values.Gamma (M := M)) : Set M := Values.gammaPullback {γ}

theorem mem_fibre (γ : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M) :
    t.val ∈ fibre γ ↔ Values.vrv t = γ.val := by
  constructor
  · rintro ⟨_,_,h⟩
    exact congrArg Subtype.val h
  · intro h
    have ht0 : t.val ≠ iRVZero := by
      intro he
      exact γ.property (h.symm.trans ((Values.vrv_eq_infinity_iff t).mpr he))
    exact ⟨t.property,ht0,Subtype.ext h⟩

theorem mem_fibre_code (γ : Values.Gamma (M := M)) (t : M) (ht : NonzeroRV t) :
    t ∈ fibre γ ↔ codeValue t = γ := by
  change t ∈ Values.gammaPullback {γ} ↔ _
  rw [SpecialTransformations.Section4.GammaSyntax.mem_gammaPullback_iff]
  exact ⟨fun h => h.2,fun h => ⟨ht,h⟩⟩

theorem subset_nonzero (γ : Values.Gamma (M := M)) : fibre γ ⊆ {t | NonzeroRV t} :=
  fun _ ⟨ht,h0,_⟩ => ⟨ht,h0⟩

theorem fibres_disjoint : Pairwise (fun γ η : Values.Gamma (M := M) => Disjoint (fibre γ) (fibre η)) := by
  intro γ η hne
  apply Set.disjoint_left.mpr
  intro t htγ htη
  let tt : CanonicalRV.RVSort M := ⟨t,(subset_nonzero γ htγ).1⟩
  have he : γ.val = η.val := ((mem_fibre γ tt).mp htγ).symm.trans ((mem_fibre η tt).mp htη)
  exact hne (Subtype.ext he)

theorem fibre_infinite (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) : (fibre γ).Infinite := by
  have hInf : (Subtype.val '' {t : CanonicalRV.RVSort M | Values.vrv t = γ.val}).Infinite :=
    (Values.infinite_gamma_fibre h00 γ).image Subtype.val_injective.injOn
  have he : Subtype.val '' {t : CanonicalRV.RVSort M | Values.vrv t = γ.val} = fibre γ := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact (mem_fibre γ t).mpr ht
    · intro hx
      let t : CanonicalRV.RVSort M := ⟨x,(subset_nonzero γ hx).1⟩
      exact ⟨t,(mem_fibre γ t).mp hx,rfl⟩
  exact he ▸ hInf

theorem finite_or_cofinite (B : FullBaseAtomicity.Base (M := M)) (A : Set M)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hARV : A ⊆ {t | iRV t}) (γ : Values.Gamma (M := M)) :
    (A ∩ fibre γ).Finite ∨ (fibre γ \ A).Finite := by
  let p := @ParameterPresentation.presentation M sM hM
  have hSpecial : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (@CanonicalStructure.normalize M sM) (Fin 1) {z | z 0 ∈ A} := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryParameters.OverBase.specialize hA
  obtain ⟨E,_,hRaw⟩ := hSpecial
  have hSorted : DefinableAt (B.real ∪ E) .rv A :=
    (@definableAt_iff_normalized_raw M sM hM (B.real ∪ E) .rv A).mpr ⟨hRaw,hARV⟩
  have hPos : Subtype.val '' Values.fibre A γ = A ∩ fibre γ := by
    ext x
    constructor
    · rintro ⟨t,⟨htγ,htA⟩,rfl⟩
      exact ⟨htA,(mem_fibre γ t).mpr htγ⟩
    · rintro ⟨hxA,hxγ⟩
      let t : CanonicalRV.RVSort M := ⟨x,hARV hxA⟩
      exact ⟨t,⟨(mem_fibre γ t).mp hxγ,hxA⟩,rfl⟩
  have hNeg : Subtype.val '' {t : CanonicalRV.RVSort M | Values.vrv t = γ.val ∧ t.val ∉ A} = fibre γ \ A := by
    ext x
    constructor
    · rintro ⟨t,⟨htγ,htA⟩,rfl⟩
      exact ⟨(mem_fibre γ t).mpr htγ,htA⟩
    · rintro ⟨hxγ,hxA⟩
      let t : CanonicalRV.RVSort M := ⟨x,(subset_nonzero γ hxγ).1⟩
      exact ⟨t,⟨(mem_fibre γ t).mp hxγ,hxA⟩,rfl⟩
  rcases rv_value_fibre_finite_or_cofinite (B.real ∪ E) A hSorted γ with hf | hf
  · exact Or.inl (hPos ▸ hf.image Subtype.val)
  · exact Or.inr (hNeg ▸ hf.image Subtype.val)

end IntegrationInACVF.Section3ACVF.FullRVValueFibres
