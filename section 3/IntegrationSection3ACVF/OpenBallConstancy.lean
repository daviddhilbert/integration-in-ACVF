import IntegrationSection3ACVF.FullGammaAtomicity
import IntegrationSection3ACVF.FullProfileCosets
import IntegrationSection3ACVF.GammaCosetGeometry
import IntegrationSection3ACVF.PaperBalls

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

/-- The full graph of a function whose domain is A. Values outside A are
not part of this graph and need not be definable. -/
def graphOn {m : ℕ} (A : Set M) (f : VFType (M := M) → Set (Fin m → M)) :
    Set (Fin (m+1) → M) :=
  BallFibreConstancy.graph f ∩ {z | z 0 ∈ A}

noncomputable def extendByEmpty {m : ℕ} (A : Set M)
    (f : VFType (M := M) → Set (Fin m → M)) (x : VFType (M := M)) : Set (Fin m → M) :=
  if x.val ∈ A then f x else ∅

theorem graph_extendByEmpty {m : ℕ} (A : Set M)
    (f : VFType (M := M) → Set (Fin m → M)) :
    BallFibreConstancy.graph (extendByEmpty A f) = graphOn A f := by
  ext z
  constructor
  · rintro ⟨x,hx,hy⟩
    have hxA : x.val ∈ A := by
      by_contra hn
      simp only [extendByEmpty,if_neg hn,Set.mem_empty_iff_false] at hy
    exact ⟨⟨x,hx,by simpa only [extendByEmpty,if_pos hxA] using hy⟩,hx ▸ hxA⟩
  · rintro ⟨⟨x,hx,hy⟩,hzA⟩
    refine ⟨x,hx,?_⟩
    simpa only [extendByEmpty,if_pos (hx.symm ▸ hzA)] using hy

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


/-- Lemma 3.9 with exactly the graph on its stated open-ball domain. -/
theorem lemma_3_9_on (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x : VFType (M := M), x.val ∈ gammaBall a α true →
      ∀ ys ∈ f x, ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (graphOn (gammaBall a α true) f)) :
    ∀ x : VFType (M := M), x.val ∈ gammaBall a α true →
      ∀ y : VFType (M := M), y.val ∈ gammaBall a α true → f x = f y := by
  let g := extendByEmpty (gammaBall a α true) f
  have hg : ∀ x ys, ys ∈ g x → ∀ i, iRV (ys i) := by
    intro x ys hys
    by_cases hx : x.val ∈ gammaBall a α true
    · exact hf x hx ys (by simpa only [g,extendByEmpty,if_pos hx] using hys)
    · simp only [g,extendByEmpty,if_neg hx,Set.mem_empty_iff_false] at hys
  have hd : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph g) := by
    rw [graph_extendByEmpty]
    exact hgraph
  have hc := lemma_3_9 h00 B δ hδ hδ1 a α hA g hg hd
  intro x hx y hy
  simpa only [g,extendByEmpty,if_pos hx,if_pos hy] using hc x hx y hy

/-- Corollary 3.10 with exactly the graph on the original atomic domain. -/
theorem corollary_3_10_on (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hsub : gammaBall a α true ⊆ A)
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x : VFType (M := M), x.val ∈ A → ∀ ys ∈ f x, ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (graphOn A f)) :
    ∀ x : VFType (M := M), x.val ∈ gammaBall a α true →
      ∀ y : VFType (M := M), y.val ∈ gammaBall a α true → f x = f y := by
  let g := extendByEmpty A f
  have hg : ∀ x ys, ys ∈ g x → ∀ i, iRV (ys i) := by
    intro x ys hys
    by_cases hx : x.val ∈ A
    · exact hf x hx ys (by simpa only [g,extendByEmpty,if_pos hx] using hys)
    · simp only [g,extendByEmpty,if_neg hx,Set.mem_empty_iff_false] at hys
  have hd : FullBaseAtomicity.OverBase B (BallFibreConstancy.graph g) := by
    rw [graph_extendByEmpty]
    exact hgraph
  have hc := corollary_3_10 h00 B δ hδ hδ1 hA a α hsub g hg hd
  intro x hx y hy
  simpa only [g,extendByEmpty,if_pos (hsub hx),if_pos (hsub hy)] using hc x hx y hy


/-- The whole VF sort cannot lie inside an atomic set: the parameter-free
singleton zero separates it from the VF point one. -/
theorem atomic_not_contains_vf (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : AdjoinBall.AtomicOver B A) : ¬ ({x : M | iVF x} ⊆ A) := by
  intro hAll
  have hz : DefinableAt B.real .vf ({iVFZero} : Set M) :=
    definableClosureAt_function_symbol B.real Fn.vfZero Fin.elim0
      (fun j => j.elim0) (fun j => j.elim0)
  have hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ ({iVFZero} : Set M)} :=
    FullBaseAtomicity.OverBase.of_real (B := B)
      (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp hz).1)
  rcases hA.2 {iVFZero} hd with hw | he
  · have h10 : (1 : VFType (M := M)).val = (0 : VFType (M := M)).val :=
      hw (hAll (1 : VFType (M := M)).property)
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext h10)
  · exact Set.disjoint_left.mp he (hAll (0 : VFType (M := M)).property)
      (show (0 : VFType (M := M)).val ∈ ({iVFZero} : Set M) from rfl)

/-- Lemma 3.9 including the sequel's whole-field open-ball convention. -/
theorem lemma_3_9_open (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x : VFType (M := M), x.val ∈ A → ∀ ys ∈ f x, ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (graphOn A f)) :
    ∀ x : VFType (M := M), x.val ∈ A → ∀ y : VFType (M := M), y.val ∈ A → f x = f y := by
  rcases ho with rfl | ⟨a,α,rfl⟩
  · exact (atomic_not_contains_vf B hA Set.Subset.rfl).elim
  · exact lemma_3_9_on h00 B δ hδ hδ1 a α hA f hf hgraph

/-- Corollary 3.10 for the sequel's exact open-ball predicate and the full
graph on the atomic domain. No radius or centre occurs in the conclusion. -/
theorem corollary_3_10_open (h00 : M ⊨ Axioms.ACVF00)
    (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A O : Set M} (hA : AdjoinBall.AtomicOver B A)
    (ho : PaperBalls.IsOpenBall O) (hsub : O ⊆ A)
    {m : ℕ} (f : VFType (M := M) → Set (Fin m → M))
    (hf : ∀ x : VFType (M := M), x.val ∈ A → ∀ ys ∈ f x, ∀ i, iRV (ys i))
    (hgraph : FullBaseAtomicity.OverBase B (graphOn A f)) :
    ∀ x : VFType (M := M), x.val ∈ O → ∀ y : VFType (M := M), y.val ∈ O → f x = f y := by
  rcases ho with rfl | ⟨a,α,rfl⟩
  · exact (atomic_not_contains_vf B hA hsub).elim
  · exact corollary_3_10_on h00 B δ hδ hδ1 hA a α hsub f hf hgraph

end IntegrationInACVF.Section3ACVF.OpenBallConstancy
