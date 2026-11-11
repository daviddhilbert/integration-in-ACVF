import IntegrationSection3ACVF.GammaFunctionSyntax
import IntegrationSection3ACVF.GammaTupleParameters
import IntegrationSection3ACVF.OrderedGermMonotonicity

/-! Full-base first-order syntax for local increasing germs and the
prefix sets used to propagate them. No pointwise graph is assumed total. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaGermSyntax

open FullGammaSyntax OrderedGermMonotonicity

variable {M β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [LinearOrder β]

theorem comparison_controller (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1))) (x : Values.Gamma (M := M)) (hx : x ∈ D) :
    ∃ F, SpecialTransformations.Section4.FiniteOrder.Controls F {y | y ∈ D ∧ f x < f y} := by
  have hd := GammaTupleParameters.specialize B (![x] : Fin 1 → Values.Gamma (M := M))
    (hCmp.reindex (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  have hScalar : Scalar (GammaTupleParameters.extend B ![x]) {y | y ∈ D ∧ f x < f y} := by
    apply (scalar_definable_iff _).mp
    apply hd.congr
    intro a
    change (x ∈ D ∧ a 0 ∈ D ∧ f x < f (a 0)) ↔ (a 0 ∈ D ∧ f x < f (a 0))
    exact ⟨fun h => h.2,fun h => ⟨hx,h⟩⟩
  exact FullGammaControllers.finite_controller h00 _ _ hScalar

def increasingSet (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β) :
    Set (Values.Gamma (M := M)) := {x | x ∈ D ∧ increasing D f x}

theorem increasing_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β) (hD : Scalar B D)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1))) : Scalar B (increasingSet D f) := by
  let ι := (Fin 1 ⊕ Fin 2) ⊕ Fin 1
  let x : ι := .inl (.inl 0)
  let l : ι := .inl (.inr 0)
  let u : ι := .inl (.inr 1)
  let y : ι := .inr 0
  have hLeft := (((unary_at hD y).and (lt_definable B l y)).and
    (lt_definable B y x)).imp (hCmp.reindex (![y,x] : Fin 2 → ι))
  have hRight := (((unary_at hD y).and (lt_definable B x y)).and
    (lt_definable B y u)).imp (hCmp.reindex (![x,y] : Fin 2 → ι))
  have hBounds := (lt_definable B (Sum.inr 0 : Fin 1 ⊕ Fin 2) (Sum.inl 0)).and
    (lt_definable B (Sum.inl 0 : Fin 1 ⊕ Fin 2) (Sum.inr 1))
  have hd := (unary_at hD (0 : Fin 1)).and
    ((hBounds.and (hLeft.forall_block.and hRight.forall_block)).exists_block)
  apply (scalar_definable_iff (increasingSet D f)).mp
  apply hd.congr
  intro a
  change (a 0 ∈ D ∧ ∃ b : Fin 2 → Values.Gamma (M := M),
    (b 0 < a 0 ∧ a 0 < b 1) ∧
    (∀ c : Fin 1 → Values.Gamma (M := M), ((c 0 ∈ D ∧ b 0 < c 0) ∧ c 0 < a 0) →
      c 0 ∈ D ∧ a 0 ∈ D ∧ f (c 0) < f (a 0)) ∧
    (∀ c : Fin 1 → Values.Gamma (M := M), ((c 0 ∈ D ∧ a 0 < c 0) ∧ c 0 < b 1) →
      a 0 ∈ D ∧ c 0 ∈ D ∧ f (a 0) < f (c 0))) ↔ _
  constructor
  · rintro ⟨hx,b,⟨hl,hu⟩,hL,hR⟩
    exact ⟨hx,⟨b 0,hl,fun y hy hly hyx => (hL ![y] ⟨⟨hy,hly⟩,hyx⟩).2.2⟩,
      ⟨b 1,hu,fun y hy hxy hyu => (hR ![y] ⟨⟨hy,hxy⟩,hyu⟩).2.2⟩⟩
  · rintro ⟨hx,⟨l,hl,hL⟩,u,hu,hR⟩
    exact ⟨hx,![l,u],⟨hl,hu⟩,
      (fun c ⟨⟨hy,hly⟩,hyx⟩ => ⟨hy,hx,hL (c 0) hy hly hyx⟩),
      (fun c ⟨⟨hy,hxy⟩,hyu⟩ => ⟨hx,hy,hR (c 0) hy hxy hyu⟩)⟩

def guardedPrefix (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (a : Fin 3 → Values.Gamma (M := M)) : Prop :=
  a 0 ≤ a 2 ∧ a 2 ≤ a 1 ∧ ∀ t, a 0 < t → t ≤ a 2 → a 0 ∈ D ∧ t ∈ D ∧ f (a 0) < f t

theorem prefix_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1))) : Definable B (guardedPrefix D f) := by
  let ι := Fin 3 ⊕ Fin 1
  have hPrem := (lt_definable B (Sum.inl 0 : ι) (Sum.inr 0)).and
    (lt_definable B (Sum.inl 2 : ι) (Sum.inr 0)).not
  have hCmp' := hCmp.reindex (![.inl 0,.inr 0] : Fin 2 → ι)
  have hd := (((lt_definable B (2 : Fin 3) 0).not).and
    ((lt_definable B (1 : Fin 3) 2).not)).and (hPrem.imp hCmp').forall_block
  apply hd.congr
  intro a
  change ((¬ a 2 < a 0 ∧ ¬ a 1 < a 2) ∧ ∀ c : Fin 1 → Values.Gamma (M := M),
    (a 0 < c 0 ∧ ¬ a 2 < c 0) → a 0 ∈ D ∧ c 0 ∈ D ∧ f (a 0) < f (c 0)) ↔ _
  simp only [not_lt]
  constructor
  · rintro ⟨⟨h0,h1⟩,h⟩
    exact ⟨h0,h1,fun t h0 h1 => h ![t] ⟨h0,h1⟩⟩
  · rintro ⟨h0,h1,h⟩
    exact ⟨⟨h0,h1⟩,fun c ⟨h0,h1⟩ => h (c 0) h0 h1⟩

theorem prefix_controller (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → β)
    (hCmp : Definable B (fun a : Fin 2 → Values.Gamma (M := M) =>
      a 0 ∈ D ∧ a 1 ∈ D ∧ f (a 0) < f (a 1)))
    (u w : Values.Gamma (M := M)) (hu : u ∈ D) (hD : Set.Icc u w ⊆ D) :
    ∃ F, SpecialTransformations.Section4.FiniteOrder.Controls F (prefixSet f u w) := by
  have hd := GammaTupleParameters.specialize B (![u,w] : Fin 2 → Values.Gamma (M := M))
    ((prefix_definable B D f hCmp).reindex (![.inl 0,.inl 1,.inr 0] : Fin 3 → Fin 2 ⊕ Fin 1))
  have hScalar : Scalar (GammaTupleParameters.extend B ![u,w]) (prefixSet f u w) := by
    apply (scalar_definable_iff _).mp
    apply hd.congr
    intro a
    change (u ≤ a 0 ∧ a 0 ≤ w ∧ ∀ t, u < t → t ≤ a 0 → u ∈ D ∧ t ∈ D ∧ f u < f t) ↔
      (a 0 ∈ Set.Icc u w ∧ ∀ t, u < t → t ≤ a 0 → f u < f t)
    constructor
    · rintro ⟨h0,h1,h⟩
      exact ⟨⟨h0,h1⟩,fun t h0 h1 => (h t h0 h1).2.2⟩
    · rintro ⟨⟨h0,h1⟩,h⟩
      exact ⟨h0,h1,fun t hut hta => ⟨hu,hD ⟨hut.le,hta.trans h1⟩,h t hut hta⟩⟩
  exact FullGammaControllers.finite_controller h00 _ _ hScalar

end IntegrationInACVF.Section3ACVF.GammaGermSyntax
