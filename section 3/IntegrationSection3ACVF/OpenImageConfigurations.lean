import IntegrationSection3ACVF.BallKindPredicates
import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3.ImaginaryBaseImages

/-! First-order finite real witnesses for failures to send an open ball
to an open ball. The original map is used only on its actual domain.
All definitions retain the full original real/Gamma/ball parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.OpenImageConfigurations

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def body (q : Fin 4 → M) : Set M :=
  {x | ∃ hq : q ∈ BallPresentation.codeDomain,
    x ∈ BallImaginaries.underlying (BallPresentation.decode ⟨q,hq⟩)}

omit hM in
theorem body_valid (q : BallPresentation.codeDomain (M := M)) :
    body q.val = BallImaginaries.underlying (BallPresentation.decode q) := by
  ext x
  exact ⟨fun ⟨_,hx⟩ => hx,fun hx => ⟨q.property,hx⟩⟩

theorem body_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B
      {z : Fin 4 ⊕ Fin 1 → M | z (.inr 0) ∈ body (z ∘ Sum.inl)} := by
  exact FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)

theorem subset_definable (B : FullBaseAtomicity.Base (M := M))
    {U : Set M} (hU : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U}) :
    FullBaseAtomicity.OverBase B {q : Fin 4 → M | body q ⊆ U} := by
  have hX := body_definable B
  have hV := hU.preimage_comp (Sum.inr : Fin 1 → Fin 4 ⊕ Fin 1)
  have h := FullBaseAtomicity.OverBase.forall_block (hX.compl.union hV)
  apply FullBaseAtomicity.OverBase.congr h
  intro q
  change (∀ x : Fin 1 → M, x 0 ∉ body q ∨ x 0 ∈ U) ↔ body q ⊆ U
  constructor
  · intro h x hx
    exact (h ![x]).resolve_left (fun hn => hn hx)
  · intro h x
    by_cases hx : x 0 ∈ body q
    · exact Or.inr (h hx)
    · exact Or.inl hx

def imageOn (A : Set M) (f : M → M) (q : Fin 4 → M) : Set M :=
  f '' (body q ∩ A)

theorem image_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B
      {z : Fin 4 ⊕ Fin 1 → M | z (.inr 0) ∈ imageOn A f (z ∘ Sum.inl)} := by
  let πb : Fin 4 ⊕ Fin 1 → (Fin 4 ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πg : Fin 2 → (Fin 4 ⊕ Fin 1) ⊕ Fin 1 := ![.inr 0,.inl (.inr 0)]
  have h := FullBaseAtomicity.OverBase.exists_block
    (((body_definable B).preimage_comp πb).inter (hf.preimage_comp πg))
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∃ x : Fin 1 → M,
    x 0 ∈ body (z ∘ Sum.inl) ∧ x 0 ∈ A ∧ z (.inr 0) = f (x 0)) ↔
      z (.inr 0) ∈ f '' (body (z ∘ Sum.inl) ∩ A)
  exact ⟨fun ⟨x,hb,ha,he⟩ => ⟨x 0,⟨hb,ha⟩,he.symm⟩,
    fun ⟨x,⟨hb,ha⟩,he⟩ => ⟨![x],hb,ha,he.symm⟩⟩

theorem image_eq_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B
      {z : Fin 4 ⊕ Fin 4 → M | imageOn A f (z ∘ Sum.inl) = body (z ∘ Sum.inr)} := by
  let πi : Fin 4 ⊕ Fin 1 → (Fin 4 ⊕ Fin 4) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πb : Fin 4 ⊕ Fin 1 → (Fin 4 ⊕ Fin 4) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inr i)) Sum.inr
  have hi := (image_definable B f hf).preimage_comp πi
  have hb := (body_definable B).preimage_comp πb
  have h := FullBaseAtomicity.OverBase.forall_block
    ((hi.inter hb).union (hi.compl.inter hb.compl))
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∀ y : Fin 1 → M,
    (y 0 ∈ imageOn A f (z ∘ Sum.inl) ∧ y 0 ∈ body (z ∘ Sum.inr)) ∨
    (y 0 ∉ imageOn A f (z ∘ Sum.inl) ∧ y 0 ∉ body (z ∘ Sum.inr))) ↔ _
  constructor
  · intro h
    ext y
    rcases h ![y] with hp | hn
    · exact iff_of_true hp.1 hp.2
    · exact iff_of_false hn.1 hn.2
  · intro h y
    by_cases hy : y 0 ∈ imageOn A f (z ∘ Sum.inl)
    · exact Or.inl ⟨hy,h ▸ hy⟩
    · exact Or.inr ⟨hy,fun hb => hy (h.symm ▸ hb)⟩

def hasOpenImage (A : Set M) (f : M → M) : Set (Fin 4 → M) :=
  {q | ∃ r ∈ BallKindPredicates.openCodes, imageOn A f q = body r}

theorem hasOpenImage_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (hasOpenImage A f) := by
  have ho := FullBaseAtomicity.OverBase.of_real (B := B)
    (BallKindPredicates.chartCodes_definable B.real).1
  exact FullBaseAtomicity.OverBase.exists_block
    ((ho.preimage_comp (Sum.inr : Fin 4 → Fin 4 ⊕ Fin 4)).inter (image_eq_definable B f hf))

def bad (A : Set M) (f : M → M) : Set (Fin 4 → M) :=
  {q | q ∈ BallKindPredicates.openCodes ∧ body q ⊆ A ∧ q ∉ hasOpenImage A f}

theorem bad_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B (bad A f) := by
  have ho := FullBaseAtomicity.OverBase.of_real (B := B)
    (BallKindPredicates.chartCodes_definable B.real).1
  exact ho.inter ((subset_definable B hA).inter (hasOpenImage_definable B f hf).compl)

theorem body_open (q : Fin 4 → M) (hq : q ∈ BallKindPredicates.openCodes) :
    PaperBalls.IsOpenBall (body q) := by
  have hv : q ∈ BallPresentation.codeDomain := hq.1
  have hOpen : PaperBalls.IsOpenBall
      (BallImaginaries.underlying (BallPresentation.decode ⟨q,hv⟩)) := by
    change BallPresentation.decode ⟨q,hv⟩ ∈
      {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)}
    rw [← BallKindPredicates.open_image_eq]
    exact ⟨q,hq,hv,rfl⟩
  rwa [body_valid (⟨q,hv⟩ : BallPresentation.codeDomain)]

theorem hasOpenImage_iff (A : Set M) (f : M → M) (q : Fin 4 → M) :
    q ∈ hasOpenImage A f ↔ PaperBalls.IsOpenBall (imageOn A f q) := by
  constructor
  · rintro ⟨r,hr,he⟩
    exact he.symm ▸ body_open r hr
  · intro ho
    have hBall : IsBall (imageOn A f q) := by
      rcases ho with hvf | ⟨a,α,he⟩
      · exact Or.inl hvf
      · exact he.symm ▸ BallEnlargementGeometry.gammaBall_isBall a α true
    obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded _ hBall
    have hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := hi.symm ▸ ho
    change i ∈ {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)} at hOpen
    rw [← BallKindPredicates.open_image_eq] at hOpen
    obtain ⟨r,hr,hvalid,he⟩ := hOpen
    change r ∈ BallPresentation.codeDomain at hvalid
    change BallPresentation.decode ⟨r,hvalid⟩ = i at he
    refine ⟨r,hr,?_⟩
    rw [body_valid (⟨r,hvalid⟩ : BallPresentation.codeDomain),he,hi]

theorem bad_iff (A : Set M) (f : M → M) (q : Fin 4 → M) :
    q ∈ bad A f ↔ q ∈ BallKindPredicates.openCodes ∧ body q ⊆ A ∧
      ¬ PaperBalls.IsOpenBall (f '' body q) := by
  change (q ∈ BallKindPredicates.openCodes ∧ body q ⊆ A ∧ q ∉ hasOpenImage A f) ↔ _
  refine and_congr_right (fun _ => and_congr_right (fun hsub => ?_))
  rw [hasOpenImage_iff]
  have he : imageOn A f q = f '' body q := by
    unfold imageOn
    rw [Set.inter_eq_left.mpr hsub]
  rw [he]

end IntegrationInACVF.Section3ACVF.OpenImageConfigurations
