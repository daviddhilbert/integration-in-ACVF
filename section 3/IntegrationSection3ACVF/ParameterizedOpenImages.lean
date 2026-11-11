import IntegrationSection3ACVF.OpenImageConfigurations
import IntegrationSection3ACVF.UnaryRelationFamilies
import IntegrationSection3ACVF.FullBaseLogic

/-! Open-image tests for uniform unary graphs. Every context label is a
free variable. Quantification is over actual four-coordinate ball codes. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.ParameterizedOpenImages

open UnaryRelationFamilies OpenImageConfigurations

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fibre (C : Set (σ ⊕ Fin 1 → M)) (p : σ → M) : Set M :=
  {x | Sum.elim p ![x] ∈ C}

def relImage (G : Set (σ ⊕ Fin 2 → M)) (p : σ → M) (D : Set M) : Set M :=
  {y | ∃ x ∈ D, pair p x y ∈ G}

def subsetCodes (C : Set (σ ⊕ Fin 1 → M)) : Set (σ ⊕ Fin 4 → M) :=
  {z | body (z ∘ Sum.inr) ⊆ fibre C (z ∘ Sum.inl)}

def ballImage (G : Set (σ ⊕ Fin 2 → M)) : Set ((σ ⊕ Fin 4) ⊕ Fin 1 → M) :=
  {z | z (.inr 0) ∈ relImage G (z ∘ Sum.inl ∘ Sum.inl)
    (body (z ∘ Sum.inl ∘ Sum.inr))}

theorem subsetCodes_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {C : Set (σ ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (subsetCodes C) := by
  let πb : Fin 4 ⊕ Fin 1 → (σ ⊕ Fin 4) ⊕ Fin 1 := Sum.map Sum.inr id
  let πc : σ ⊕ Fin 1 → (σ ⊕ Fin 4) ⊕ Fin 1 := Sum.map Sum.inl id
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B
    (FullBaseAtomicity.OverBase.preimage_comp (body_definable B) πb)
    (FullBaseAtomicity.OverBase.preimage_comp hC πc))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  have he (x : Fin 1 → M) : Sum.elim z x ∘ πc = Sum.elim (z ∘ Sum.inl) ![x 0] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k; rfl
  change (∀ x : Fin 1 → M, x 0 ∈ body (z ∘ Sum.inr) → Sum.elim z x ∘ πc ∈ C) ↔ _
  simp_rw [he]
  exact ⟨fun h x hx => h ![x] hx,fun h x hx => h hx⟩

theorem ballImage_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G) :
    FullBaseAtomicity.OverBase B (ballImage G) := by
  let πb : Fin 4 ⊕ Fin 1 → ((σ ⊕ Fin 4) ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun k => .inl (.inl (.inr k))) Sum.inr
  let πg : σ ⊕ Fin 2 → ((σ ⊕ Fin 4) ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun k => .inl (.inl (.inl k))) (![.inr 0,.inl (.inr 0)] : Fin 2 → _)
  have he (z : (σ ⊕ Fin 4) ⊕ Fin 1 → M) (x : Fin 1 → M) :
      Sum.elim z x ∘ πg = pair (z ∘ Sum.inl ∘ Sum.inl) (x 0) (z (.inr 0)) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp (body_definable B) πb)
    (FullBaseAtomicity.OverBase.preimage_comp hG πg))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ x : Fin 1 → M, x 0 ∈ body (z ∘ Sum.inl ∘ Sum.inr) ∧ Sum.elim z x ∘ πg ∈ G) ↔ _
  simp_rw [he]
  exact ⟨fun ⟨x,hx,hg⟩ => ⟨x 0,hx,hg⟩,fun ⟨x,hx,hg⟩ => ⟨![x],hx,hg⟩⟩

def imageEquals (G : Set (σ ⊕ Fin 2 → M)) : Set ((σ ⊕ Fin 4) ⊕ Fin 4 → M) :=
  {z | relImage G (z ∘ Sum.inl ∘ Sum.inl) (body (z ∘ Sum.inl ∘ Sum.inr)) =
    body (z ∘ Sum.inr)}

theorem imageEquals_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G) :
    FullBaseAtomicity.OverBase B (imageEquals G) := by
  let πi : (σ ⊕ Fin 4) ⊕ Fin 1 → ((σ ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 1 := Sum.map Sum.inl id
  let πb : Fin 4 ⊕ Fin 1 → ((σ ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 1 := Sum.map Sum.inr id
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.equivalence B
    (FullBaseAtomicity.OverBase.preimage_comp (ballImage_definable B hG) πi)
    (FullBaseAtomicity.OverBase.preimage_comp (body_definable B) πb))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∀ y : Fin 1 → M,
    y 0 ∈ relImage G (z ∘ Sum.inl ∘ Sum.inl) (body (z ∘ Sum.inl ∘ Sum.inr)) ↔
      y 0 ∈ body (z ∘ Sum.inr)) ↔ _
  exact ⟨fun h => Set.ext (fun y => h ![y]),fun h y => Set.ext_iff.mp h (y 0)⟩

def hasOpenImage (G : Set (σ ⊕ Fin 2 → M)) : Set (σ ⊕ Fin 4 → M) :=
  {z | ∃ r ∈ BallKindPredicates.openCodes,
    relImage G (z ∘ Sum.inl) (body (z ∘ Sum.inr)) = body r}

theorem hasOpenImage_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G) :
    FullBaseAtomicity.OverBase B (hasOpenImage G) := by
  have ho := FullBaseAtomicity.OverBase.of_real (B := B)
    (BallKindPredicates.chartCodes_definable B.real).1
  exact FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp ho (Sum.inr : Fin 4 → (σ ⊕ Fin 4) ⊕ Fin 4))
    (imageEquals_definable B hG))

def good (G : Set (σ ⊕ Fin 2 → M)) (C : Set (σ ⊕ Fin 1 → M)) : Set (σ → M) :=
  {p | ∀ q ∈ BallKindPredicates.openCodes, body q ⊆ fibre C p →
    Sum.elim p q ∈ hasOpenImage G}

theorem good_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {C : Set (σ ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (good G C) := by
  have ho := FullBaseAtomicity.OverBase.of_real (B := B)
    (BallKindPredicates.chartCodes_definable B.real).1
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B
    (FullBaseAtomicity.OverBase.inter
      (FullBaseAtomicity.OverBase.preimage_comp ho (Sum.inr : Fin 4 → σ ⊕ Fin 4))
      (subsetCodes_definable B hC)) (hasOpenImage_definable B hG))
  apply FullBaseAtomicity.OverBase.congr hd
  intro p
  change (∀ q : Fin 4 → M, (q ∈ BallKindPredicates.openCodes ∧ body q ⊆ fibre C p) →
    Sum.elim p q ∈ hasOpenImage G) ↔ _
  exact ⟨fun h q hq hsub => h q ⟨hq,hsub⟩,fun h q hq => h q hq.1 hq.2⟩

theorem exists_open_code {D : Set M} (hD : PaperBalls.IsOpenBall D) :
    ∃ q ∈ BallKindPredicates.openCodes, body q = D := by
  have hb : IsBall D := by
    rcases hD with h | ⟨a,α,h⟩
    · exact Or.inl h
    · exact h.symm ▸ BallEnlargementGeometry.gammaBall_isBall a α true
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded D hb
  have ho : PaperBalls.IsOpenBall (BallImaginaries.underlying i) := hi.symm ▸ hD
  change i ∈ {i | PaperBalls.IsOpenBall (BallImaginaries.underlying i)} at ho
  rw [← BallKindPredicates.open_image_eq] at ho
  obtain ⟨q,hq,hv,he⟩ := ho
  change q ∈ BallPresentation.codeDomain at hv
  change BallPresentation.decode ⟨q,hv⟩ = i at he
  exact ⟨q,hq,(body_valid (⟨q,hv⟩ : BallPresentation.codeDomain)).trans (congrArg BallImaginaries.underlying he) |>.trans hi⟩

theorem good_iff (G : Set (σ ⊕ Fin 2 → M)) (C : Set (σ ⊕ Fin 1 → M)) (p : σ → M) :
    p ∈ good G C ↔ ∀ D ⊆ fibre C p, PaperBalls.IsOpenBall D →
      PaperBalls.IsOpenBall (relImage G p D) := by
  constructor
  · intro h D hDC hDo
    obtain ⟨q,hq,hqD⟩ := exists_open_code hDo
    obtain ⟨r,hr,he⟩ := h q hq (hqD.symm ▸ hDC)
    change relImage G p (body q) = body r at he
    exact (hqD ▸ he).symm ▸ body_open r hr
  · intro h q hq hqC
    obtain ⟨r,hr,he⟩ := exists_open_code (h (body q) hqC (body_open q hq))
    exact ⟨r,hr,he.symm⟩

end IntegrationInACVF.Section3ACVF.ParameterizedOpenImages
