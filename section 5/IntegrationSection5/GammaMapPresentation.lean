import IntegrationSection5.GammaPreparation

/-! A common real presentation is constructed internally from finite
Gamma codes for the two domains and the complete graph. No code is named
in the original base or added to the smallness hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {n m u w : ℕ}

theorem common_gamma_presentation
    (A : Set (Point (M := M) n m)) (B : Set (Point (M := M) u w)) (f : A → B)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hf : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ S : Set M, P.real ⊆ S ∧ SetDefinable (pointSpace n m) S A ∧
      SetDefinable (pointSpace u w) S B ∧
      RelationDefinable (pointSpace n m) (pointSpace u w) S
        (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q) := by
  obtain ⟨_, tA, _, DA, hDA⟩ := gammaPresentationInput P A hA
  obtain ⟨_, tB, _, DB, hDB⟩ := gammaPresentationInput P B hB
  obtain ⟨_, tF, hF⟩ := GammaGraphDefinable.real_specialize hf
  let SA := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tA)
  let SB := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tB)
  let SF := P.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple tF)
  let S := (SA ∪ SB) ∪ SF
  have hAS : SA ⊆ S := fun _ h => Or.inl (Or.inl h)
  have hBS : SB ⊆ S := fun _ h => Or.inl (Or.inr h)
  have hFS : SF ⊆ S := fun _ h => Or.inr h
  refine ⟨S, (fun _ h => hAS (Or.inl h)), ?_, ?_, ?_⟩
  · exact hDA ▸ SetDefinable.mono _ (setDefinable DA) hAS
  · exact hDB ▸ SetDefinable.mono _ (setDefinable DB) hBS
  · exact RelationDefinable.mono _ _ hF hFS

/-- Lemma 5.1 over a genuine original real/Gamma base. The existential real
presentation changes no source, target or function. Both special chains and
the conjugate have full invariant graphs over P, not merely over the codes. -/
theorem lemma_5_1 {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (F : SpecialTransformations.Section3.VFFieldBase P.real)
    (A : Set (Point (M := M) n m)) (B : Set (Point (M := M) u w)) (f : A → B)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hf : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ S : Set M,
    ∃ hAr : SetDefinable (pointSpace n m) S A,
    ∃ hBr : SetDefinable (pointSpace u w) S B,
    ∃ hfr : RelationDefinable (pointSpace n m) (pointSpace u w) S
      (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S n r, ∃ B' : DefSet (M := M) S u s,
    ∃ TA : SpecialBijection (PresentedSet.mk A hAr) A',
    ∃ TB : SpecialBijection (PresentedSet.mk B hBr) B',
      GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
      IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
      Contractible (Map.comp TB.toMap (Map.comp (Map.mk f hfr) TA.inverseMap)) ∧
      GammaGraphDefinable P
        (pointMapGraph (Map.comp TB.toMap (Map.comp (Map.mk f hfr) TA.inverseMap))) := by
  obtain ⟨S, hPS, hAr, hBr, hfr⟩ := common_gamma_presentation A B f hA hB hf
  refine ⟨S, hAr, hBr, hfr, ?_⟩
  exact lemma_5_1_gamma_presented hs h00 hsmall F hPS
    (A := PresentedSet.mk A hAr) (B := PresentedSet.mk B hBr)
    hA hB (Map.mk f hfr) hf

end IntegrationInACVF.Section5
