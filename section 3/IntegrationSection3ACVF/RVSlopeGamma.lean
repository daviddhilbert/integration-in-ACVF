import IntegrationSection3ACVF.RVSlopeConstancy
import Section3.GammaRVSeparation

/-! Descent of the RV slope to actual Gamma and finite image under the
genuine saturation and small-base hypotheses of the checked finite
projection theorem. Every nonzero RV code of each Gamma input is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.RVSlopeGamma

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def relation (A : Set M) (f : M → M) (γ : Values.Gamma (M := M)) (c : M) : Prop :=
  (Values.fibre (RVSlopeFiniteCofinite.row A f c) γ).Nonempty

theorem sorted {A : Set M} {f : M → M} {γ : Values.Gamma (M := M)} {c : M}
    (h : relation A f γ c) : iRV c := by
  obtain ⟨t,_,ht⟩ := h
  exact ht.2.1.1

theorem graph_definable (B : FullBaseAtomicity.Base (M := M)) {A : Set M} {f : M → M}
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B
      {z : Fin 2 → M | NonzeroRV (z 0) ∧ relation A f (codeValue (z 0)) (z 1)} := by
  have hs := slopes_definable B hf
  have hsame : FullBaseAtomicity.OverBase B {z : Fin 2 → M | SameScalar (z 0) (z 1)} := by
    apply FullBaseAtomicity.OverBase.of_real
    have he : {z : Fin 2 → M |
        @SameScalar M (CanonicalStructure.normalize (M := M)) (z 0) (z 1)} =
        {z | @SameScalar M sM (z 0) (z 1)} := Set.ext (fun z => same_scalar_normalize _ _)
    exact he ▸ @same_scalar_definable M (CanonicalStructure.normalize (M := M)) B.real
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hsame
      (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp hs
      (![.inr 0,.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ u : Fin 1 → M, SameScalar (z 0) (u 0) ∧ ![u 0,z 1] ∈ slopes A f) ↔
    (NonzeroRV (z 0) ∧ ∃ t : CanonicalRV.RVSort M,
      Values.vrv t = (codeValue (z 0)).val ∧ ![t.val,z 1] ∈ slopes A f)
  have hvalue (ha : NonzeroRV (z 0)) :
      (codeValue (z 0)).val = Values.vrv (⟨z 0,ha.1⟩ : CanonicalRV.RVSort M) := by
    simp only [codeValue,dite_eq_left ha]
    rfl
  constructor
  · rintro ⟨u,hSame,hSlope⟩
    have he := (Values.vrv_eq_iff (⟨z 0,hSame.1.1⟩ : CanonicalRV.RVSort M)
      ⟨u 0,hSame.2.1.1⟩).mpr hSame.2.2
    exact ⟨hSame.1,⟨u 0,hSame.2.1.1⟩,he.symm.trans (hvalue hSame.1).symm,hSlope⟩
  · rintro ⟨ha,t,ht,hSlope⟩
    have he := (Values.vrv_eq_iff (⟨z 0,ha.1⟩ : CanonicalRV.RVSort M) t).mp
      ((hvalue ha).symm.trans ht.symm)
    exact ⟨![t.val],⟨ha,hSlope.1,he⟩,hSlope⟩

theorem finite_image {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A) :
    {c : M | ∃ γ : Values.Gamma (M := M), relation A f γ c}.Finite := by
  have hG := graph_definable B hf
  let p := @ParameterPresentation.presentation M sM hM
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
        {z | NonzeroRV (z 0) ∧ relation A f (codeValue (z 0)) (z 1)} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hG
  obtain ⟨F,hF,hd⟩ := hex
  let G : GammaRVFamily (B.real ∪ F) := {
    relation := relation A f
    sorted := fun _ _ h => sorted h
    definable := hd }
  have hrows (γ : Values.Gamma (M := M)) : {c | G.relation γ c}.Finite := by
    apply Set.Subsingleton.finite
    intro c hc d hd
    exact RVSlopeConstancy.on_value_fibre B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ hc hd
  exact G.finite_projection hκ hs h00 (small_union_finite hκ B.real hsmall F hF) hrows

end IntegrationInACVF.Section3ACVF.RVSlopeGamma
