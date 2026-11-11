import IntegrationSection3ACVF.GammaLinearBallRow
import IntegrationSection3ACVF.RealParameterTuples
import IntegrationSection3ACVF.GammaLinearRadiusClosure

/-! The actual linear-radius locus is definable over the original
interpreted base plus exactly the real centre. No choice or radius
definability hypothesis is assumed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.GammaLinearRadiusSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem locus_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (c : VFType (M := M)) :
    FullGammaSyntax.Scalar (RealParameterTuples.extend B ![c.val])
      (GammaLinearRadiusClosure.locus A f hfVF c) := by
  let C := RealParameterTuples.extend B ![c.val]
  have hRow := RealParameterTuples.specialize B (![c.val] : Fin 1 → M)
    (FullBaseAtomicity.OverBase.preimage_comp (GammaLinearBallRow.row_definable B A f hf)
      (![.inr 0,.inr 1,.inl 0] : Fin 3 → Fin 1 ⊕ Fin 2))
  have hRow' : FullBaseAtomicity.OverBase C
      {z : Fin 2 → M | GammaLinearBallRow.row A f ![z 0,z 1,c.val]} := by
    apply FullBaseAtomicity.OverBase.congr hRow
    intro z
    have he : Sum.elim (![c.val] : Fin 1 → M) z ∘
        (![.inr 0,.inr 1,.inl 0] : Fin 3 → Fin 1 ⊕ Fin 2) = ![z 0,z 1,c.val] := by
      funext i
      fin_cases i <;> rfl
    change GammaLinearBallRow.row A f (Sum.elim (![c.val] : Fin 1 → M) z ∘ _) ↔ _
    rw [he]
    rfl
  have hProper := FullGammaSyntax.proper_definable (ι := Fin 2) C
  have hd := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.inter hProper hRow')
      (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  apply FullBaseAtomicity.OverBase.congr hd
  intro a
  have he (b : Fin 1 → M) : Sum.elim a b ∘
      (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1) = ![a 0,b 0] := by
    funext i
    fin_cases i <;> rfl
  change (∃ b : Fin 1 → M, GammaSyntax.Proper (Sum.elim a b ∘ _) ∧
    GammaLinearBallRow.row A f ![a 0,b 0,c.val]) ↔ _
  simp_rw [he]
  change (∃ b : Fin 1 → M, GammaSyntax.Proper (![a 0,b 0] : Fin 2 → M) ∧
    GammaLinearBallRow.row A f ![a 0,b 0,c.val]) ↔ a 0 ∈ Values.gammaPullback (GammaLinearRadiusClosure.locus A f hfVF c)
  rw [GammaSyntax.mem_gammaPullback_iff]
  constructor
  · rintro ⟨b,hProper,hRow⟩
    exact ⟨hProper 0,codeValue (b 0),(GammaLinearBallRow.row_iff A f hfVF (a 0) (b 0)
      (hProper 0) (hProper 1) c).mp hRow⟩
  · rintro ⟨ha,s,hs⟩
    obtain ⟨t,ht,hValue⟩ := EndpointLogic.codeValue_surjective s
    have hRow : GammaLinearBallRow.row A f ![a 0,t,c.val] := by
      apply (GammaLinearBallRow.row_iff A f hfVF (a 0) t ha ht c).mpr
      rwa [hValue]
    refine ⟨![t],?_,hRow⟩
    intro i
    fin_cases i
    · exact ha
    · exact ht

end IntegrationInACVF.Section3ACVF.GammaLinearRadiusSyntax
