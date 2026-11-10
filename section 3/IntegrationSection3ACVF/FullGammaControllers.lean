import IntegrationSection3ACVF.FullGammaSyntax
import IntegrationSection3ACVF.AdjoinGamma
import Section4.GammaOrderControllers

/-! Finite order controllers for sets definable over the full original
Gamma/ball base, by specializing finite imaginary support only inside the
proof. Fixed Gamma arguments use their full named value fibres. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaControllers

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem specialize (B : FullBaseAtomicity.Base (M := M))
    (A : Set (Values.Gamma (M := M))) (hA : FullGammaSyntax.Scalar B A) :
    ∃ Q : Set M, Values.GammaDefinable Q A := by
  let p := @ParameterPresentation.presentation M sM hM
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M)) (Fin 1)
        {z | z 0 ∈ Values.gammaPullback A} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hA
  obtain ⟨F,_,hF⟩ := hex
  exact ⟨B.real ∪ F,(@definableAt_iff_normalized_raw M sM hM _ .rv _).mpr
    ⟨hF,fun _ h => h.choose⟩⟩

theorem finite_controller (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M)) (A : Set (Values.Gamma (M := M)))
    (hA : FullGammaSyntax.Scalar B A) :
    ∃ F, FiniteOrder.Controls F A := by
  obtain ⟨Q,hQ⟩ := specialize B A hA
  have hB := GammaParameters.real_definableAtBase
    (⟨Q,∅⟩ : GammaParameters.Base (M := M)) .rv (Values.gammaPullback A) hQ
  obtain ⟨F,⟨hF,_⟩,_⟩ := exists_unique_gamma_order_controller h00 ⟨Q,∅⟩ A hB
  exact ⟨F,hF⟩

theorem fix_last (B : FullBaseAtomicity.Base (M := M))
    {P : (Fin 2 → Values.Gamma (M := M)) → Prop} (hP : FullGammaSyntax.Definable B P)
    (η : Values.Gamma (M := M)) (hη : FullGammaSyntax.Scalar B {η}) :
    FullGammaSyntax.Definable B (fun a : Fin 1 → Values.Gamma (M := M) => P ![a 0,η]) := by
  let π : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inl 0,.inr 0]
  have h := ((hP.reindex π).and (FullGammaSyntax.unary_at hη (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1))).exists_block
  apply h.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M),
      P (Sum.elim a b ∘ π) ∧ b 0 ∈ ({η} : Set (Values.Gamma (M := M)))) ↔ P ![a 0,η]
  constructor
  · rintro ⟨b,hb,he⟩
    have ht : Sum.elim a b ∘ π = ![a 0,η] := by
      funext i
      fin_cases i
      · rfl
      · exact he
    exact ht ▸ hb
  · intro hp
    refine ⟨![η],?_,rfl⟩
    have ht : Sum.elim a (![η] : Fin 1 → Values.Gamma (M := M)) ∘ π = ![a 0,η] := by
      funext i
      fin_cases i <;> rfl
    exact ht.symm ▸ hp

end IntegrationInACVF.Section3ACVF.FullGammaControllers
