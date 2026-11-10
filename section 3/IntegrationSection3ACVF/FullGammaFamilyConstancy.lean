import IntegrationSection3ACVF.FullGammaAtomicity
import IntegrationSection3ACVF.AtomicCanonicalRegions

/-! A definable actual-Gamma invariant is constant on a disjoint
definable family inside an atomic VF set. The family may be infinite. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaFamilyConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The full graph includes every proper Gamma representative and every
valid ball code. No finite-image or previously named output is assumed. -/
def Graph (T : Set (BallImaginaries.Ball M))
    (f : BallImaginaries.Ball M → Values.Gamma (M := M)) :
    Set (Fin 1 ⊕ Fin 4 → M) :=
  AdjoinGamma.vectorPullback (fun γ =>
    (@BallPresentation.presentation M sM hM).pullback {j | j ∈ T ∧ f j = γ})

theorem graph_of_fibres (B : FullBaseAtomicity.Base (M := M))
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (f : BallImaginaries.Ball M → Values.Gamma (M := M))
    (C : BallImaginaries.Ball M → Set M) (hC : FullBaseAtomicity.Relation B C)
    (hEq : ∀ j ∈ T, ∀ t : M, t ∈ C j ↔ t ∈ Values.gammaPullback {f j}) :
    FullBaseAtomicity.OverBase B (Graph T f) := by
  let D := fun j => {t | j ∈ T ∧ t ∈ C j}
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hD : FullBaseAtomicity.Relation B D := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.restrict hp hT hC
  have hd := FullBaseAtomicity.OverBase.preimage_comp hD
    (Sum.swap : Fin 4 ⊕ Fin 1 → Fin 1 ⊕ Fin 4)
  change FullBaseAtomicity.OverBase B (Graph T f)
  convert hd using 1
  ext z
  change (GammaParameters.NonzeroRV (z (.inl 0)) ∧
      ∃ hc : z ∘ Sum.inr ∈ q.codes,
        q.decode ⟨z ∘ Sum.inr,hc⟩ ∈ T ∧
          f (q.decode ⟨z ∘ Sum.inr,hc⟩) = GammaParameters.codeValue (z (.inl 0))) ↔
    (∃ hc : z ∘ Sum.inr ∈ q.codes,
      q.decode ⟨z ∘ Sum.inr,hc⟩ ∈ T ∧ z (.inl 0) ∈ C (q.decode ⟨z ∘ Sum.inr,hc⟩))
  constructor
  · rintro ⟨hγ,hc,hj,he⟩
    refine ⟨hc,hj,(hEq _ hj _).mpr ?_⟩
    apply (GammaSyntax.mem_gammaPullback_iff _ _).mpr
    exact ⟨hγ,he.symm⟩
  · rintro ⟨hc,hj,ht⟩
    have hv := (GammaSyntax.mem_gammaPullback_iff _ _).mp ((hEq _ hj _).mp ht)
    exact ⟨hv.1,hc,hj,hv.2.symm⟩

theorem constant (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T)
    {C : BallImaginaries.Ball M → Set M} (hC : FullBaseAtomicity.Relation B C)
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (f : BallImaginaries.Ball M → Values.Gamma (M := M))
    (hf : FullBaseAtomicity.OverBase B (Graph T f))
    {j k : BallImaginaries.Ball M} (hj : j ∈ T) (hk : k ∈ T) : f j = f k := by
  let γ := f j
  let Bγ := B.adjoin (Sum.inr γ)
  let P := {i : BallImaginaries.Ball M | i ∈ T ∧ f i = γ}
  have hAγ := FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hA γ
  have hTγ : FullBaseAtomicity.Family Bγ T :=
    FullBaseAtomicity.OverBase.mono hT Set.Subset.rfl (Set.subset_insert _ _)
  have hCγ : FullBaseAtomicity.Relation Bγ C :=
    FullBaseAtomicity.OverBase.mono hC Set.Subset.rfl (Set.subset_insert _ _)
  have hfγ : FullBaseAtomicity.OverBase Bγ (Graph T f) :=
    FullBaseAtomicity.OverBase.mono hf Set.Subset.rfl (Set.subset_insert _ _)
  have hnamed : FullGammaSyntax.Scalar Bγ {γ} :=
    AdjoinGamma.named_scalar γ (Set.mem_insert _ _)
  have hPγ : FullBaseAtomicity.Family Bγ P := AdjoinGamma.fibre_definable hfγ γ hnamed
  have hp := ParameterPresentation.codeDomain_definable (M := M) Bγ.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  rcases AtomicRegions.uniform_property hp hAγ.2 hTγ hPγ hCγ hne hsub hdis with hall | hnone
  · exact (hall hk).2.symm
  · exact (Set.disjoint_left.mp hnone hj ⟨hj,rfl⟩).elim

end IntegrationInACVF.Section3ACVF.FullGammaFamilyConstancy
