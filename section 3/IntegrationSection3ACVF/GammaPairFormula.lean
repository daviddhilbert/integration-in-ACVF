import IntegrationSection3ACVF.GammaSpecialization
import IntegrationSection3ACVF.MultivariatePolynomialSupport

/-! A Gamma-only full base admits a two-VF-variable QF presentation with
coefficients in exactly the original real VF parameter field. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.GammaPairFormula

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem presentation (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    (G : Set (M × M))
    (hG : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ G}) :
    ∃ T : Set M, T.Finite ∧
      ∃ p : Parameters (B.real ∪ T), ∃ ψ : LRV.BoundedFormula (Fin p.length) 2,
        ψ.IsQF ∧ WellSorted p.sorts (fun _ => .vf) ψ ∧
          (∀ i (hi : iVF (p.values i)),
            (⟨p.values i,hi⟩ : VFType (M := M)) ∈ vfParameterField B.real) ∧
          ∀ x y : VFType (M := M),
            ψ.Realize p.values ![x.val,y.val] ↔ (x.val,y.val) ∈ G := by
  obtain ⟨T,hfin,hdef,hfield⟩ := GammaSpecialization.specialize_preserving_field B hOnly hG
  let S := B.real ∪ T
  let D : Set (Fin 2 → M) := {z | (∀ i, @iVF M sM (z i)) ∧ (z 0,z 1) ∈ G}
  have hVF := ((@definableAt_iff_normalized_raw M sM hM S .vf _).mp
    (@definableAt_sort M sM S .vf)).1
  have hguard : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 2)
      {z | ∀ i, @iVF M sM (z i)} := by
    letI := @CanonicalStructure.normalize M sM
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite fun i => hVF.preimage_comp (fun _ : Fin 1 => i)
  have hD : DefinableOver S (fun _ => .vf) D := by
    apply (definableOver_iff_normalized_raw S (fun _ => .vf) D).mpr
    have hraw : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 2) D := by
      letI := @CanonicalStructure.normalize M sM
      exact hguard.inter hdef
    exact ⟨hraw,fun z hz => hz.1⟩
  obtain ⟨p,ψ,hqf,hws,hψ⟩ := hD.quantifier_free hM
  have hp (i : Fin p.length) (hi : iVF (p.values i)) :
      (⟨p.values i,hi⟩ : VFType (M := M)) ∈ vfParameterField B.real := by
    rw [← hfield]
    exact Subfield.subset_closure (p.mem_base i)
  refine ⟨T,hfin,p,ψ,hqf,hws,hp,?_⟩
  intro x y
  have hsort : ∀ i, @iVF M sM ((![x.val,y.val] : Fin 2 → M) i) := by
    intro i
    fin_cases i
    · exact x.property
    · exact y.property
  constructor
  · intro h
    have hd : ![x.val,y.val] ∈ D := by
      rw [hψ]
      exact ⟨hsort,h⟩
    exact hd.2
  · intro h
    have hd : ![x.val,y.val] ∈ D := ⟨hsort,h⟩
    rw [hψ] at hd
    exact hd.2

end IntegrationInACVF.Section3ACVF.GammaPairFormula
