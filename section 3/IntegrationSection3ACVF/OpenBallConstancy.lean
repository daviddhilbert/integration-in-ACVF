import IntegrationSection3ACVF.FullGammaAtomicity
import IntegrationSection3ACVF.FullProfileCosets
import IntegrationSection3ACVF.GammaCosetGeometry

/-! Lemma 3.9 for proper open balls, with every finite RV output arity and
an arbitrary original real/Gamma/ball base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OpenBallConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Lemma 3.9. The full graph is allowed to give arbitrary values outside
this open ball; only its original-base definability is used. -/
theorem lemma_3_9 (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph f)) :
    ∀ x : VFType (M := M), x.val ∈ gammaBall a α true →
      ∀ y : VFType (M := M), y.val ∈ gammaBall a α true → f x = f y := by
  intro x hx y hy
  by_cases he : x = y
  · exact congrArg f he
  obtain ⟨β,hαβ,hβxy⟩ := GammaCosetGeometry.intermediate_radius a α x y hx hy he
  let C := B.adjoin (Sum.inr β)
  have hAC : AdjoinBall.AtomicOver C (gammaBall a α true) :=
    FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hA β
  have hβ : FullGammaSyntax.Scalar C {β} :=
    AdjoinGamma.named_scalar β (Set.mem_insert _ _)
  obtain ⟨H,hH,hballs⟩ := FullGammaRadius.gamma_subgroup C β hβ true
  have hgraphC : FullBaseAtomicity.OverBase C (BallFibreConstancy.graph f) :=
    FullBaseAtomicity.OverBase.mono hgraph Set.Subset.rfl (Set.subset_insert _ _)
  have hinf := GammaCosetGeometry.infinite_gamma_cosets h00 H β hballs a α hαβ
  have hc := FullProfileCosets.constant_on_cosets h00 C H hH hAC f hf hgraphC hinf
  exact hc x hx y hy (GammaCosetGeometry.same_coset_of_difference H β hballs x y hβxy)


/-- Corollary 3.10 for every ordinary proper open subball. Its radius need
not be definable over the original base: Lemma 3.3 first adjoins that value,
then Lemma 3.4 adjoins the actual ball name. The conclusion names neither. -/
theorem corollary_3_10 (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hsub : gammaBall a α true ⊆ A)
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x ys, ys ∈ f x → ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph f)) :
    ∀ x : VFType (M := M), x.val ∈ gammaBall a α true →
      ∀ y : VFType (M := M), y.val ∈ gammaBall a α true → f x = f y := by
  let C := B.adjoin (Sum.inr α)
  have hAC : AdjoinBall.AtomicOver C A :=
    FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hA α
  have hα : FullGammaSyntax.Scalar C {α} := AdjoinGamma.named_scalar α (Set.mem_insert _ _)
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded a α
  let D := C.adjoin (Sum.inl i)
  have hAT : FullBallCoset.CompleteType C A := hAC.2
  have hb := FullGammaRadius.lemma_3_4 C α hα true hAT i a hi (by rwa [hi])
  have hball : AdjoinBall.AtomicOver D (gammaBall a α true) := by
    change AdjoinBall.AtomicOver D (BallImaginaries.underlying i) at hb
    rwa [hi] at hb
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  have hδD : FullGammaSyntax.Scalar D {δ} :=
    FullBaseAtomicity.OverBase.mono hδC Set.Subset.rfl (Set.subset_insert _ _)
  have hfC : FullBaseAtomicity.OverBase C (BallFibreConstancy.graph f) :=
    FullBaseAtomicity.OverBase.mono hgraph Set.Subset.rfl (Set.subset_insert _ _)
  have hfD : FullBaseAtomicity.OverBase D (BallFibreConstancy.graph f) :=
    FullBaseAtomicity.OverBase.mono hfC Set.Subset.rfl (Set.subset_insert _ _)
  exact lemma_3_9 h00 D δ hδD hδ1 a α hball f hf hfD

end IntegrationInACVF.Section3ACVF.OpenBallConstancy
