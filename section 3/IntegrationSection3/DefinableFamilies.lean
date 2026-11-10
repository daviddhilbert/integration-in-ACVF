module

public import IntegrationSection3.Atomicity
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Definable unary families over their original parameter base

The parameter promotion proof is the unary specialization of the generic
`SpecialTransformations.ModelTheory.promote_definable_tuple_fibre` in the
pinned predecessor's `Section3/GammaBaseTools.lean`. It is adapted here to
Mathlib's generic language interface, so it can be checked without importing
the entire ACVF coordination root. No model-theoretic conclusion is assumed.
-/

open Set FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.DefinableFamilies

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {Q : Set M}

def fibre (R : Set (M × M)) (t : M) : Set M := {x | (t, x) ∈ R}

def domain (R : Set (M × M)) : Set M := {t | ∃ x, (t, x) ∈ R}

/-- Algebraicity means membership in a finite definable set over this exact base.
This is generic first-order algebraicity, not an additional ACVF assumption. -/
def IsAlgebraicPoint (L : Language.{u, v}) [L.Structure M] (Q : Set M) (t : M) : Prop :=
  ∃ S : Set M, Q.Definable₁ L S ∧ S.Finite ∧ t ∈ S

theorem isAlgebraicPoint_of_mem {S : Set M} (hS : Q.Definable₁ L S)
    (hfinite : S.Finite) {t : M} (ht : t ∈ S) : IsAlgebraicPoint L Q t :=
  ⟨S, hS, hfinite, ht⟩

/-- A unary relation's first projection is definable over the same base. -/
theorem definable_domain {R : Set (M × M)} (hR : Q.Definable₂ L R) :
    Q.Definable₁ L (domain R) := by
  have hp := hR.image_comp (fun _ : Fin 1 => (0 : Fin 2))
  change Q.Definable L {z : Fin 1 → M | ∃ x, (z 0, x) ∈ R}
  convert hp using 1
  ext z
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨![z 0, x], hx, ?_⟩
    funext i
    fin_cases i
    rfl
  · rintro ⟨a, ha, haz⟩
    have he : a 0 = z 0 := congrFun haz 0
    change (a 0, a 1) ∈ R at ha
    exact ⟨a 1, by simpa only [he] using ha⟩

/-- Naming the index suffices to define its fibre; no other parameter is added. -/
theorem definable_fibre {R : Set (M × M)} (hR : Q.Definable₂ L R) (t : M) :
    (insert t Q).Definable₁ L (fibre R t) := by
  have hm := hR.mono (Set.subset_insert t Q)
  have hf : (insert t Q).DefinableMap L (fun z : Fin 1 → M => ![t, z 0]) := by
    intro i
    fin_cases i
    · exact L.definableFun_const _ (Set.mem_insert t Q)
    · exact Set.DefinableFun.proj L
  exact hm.preimage_map hf

/-- Promote the additional named index into a free variable.
This is a syntactic theorem, not a uniformity hypothesis about a chosen set. -/
theorem promote_fibre (Q : Set M) (t : M) (S : Set M)
    (hS : (insert t Q).Definable₁ L S) :
    ∃ R : Set (M × M), Q.Definable₂ L R ∧ fibre R t = S := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hS
  let g : (↥(insert t Q) ⊕ Fin 1) → Q ⊕ Fin 2 :=
    Sum.elim (fun a => if ha : a.val ∈ Q then Sum.inl ⟨a.val, ha⟩ else Sum.inr 0)
      (fun _ => Sum.inr 1)
  let ψ : L.Formula (Q ⊕ Fin 2) := φ.relabel g
  let R : Set (M × M) := {p | ψ.Realize (Sum.elim Subtype.val ![p.1, p.2])}
  have hreal (x : M) : (t, x) ∈ R ↔ x ∈ S := by
    change (φ.relabel g).Realize (Sum.elim Subtype.val ![t, x]) ↔ x ∈ S
    rw [Formula.realize_relabel]
    have he : Sum.elim (Subtype.val : Q → M) ![t, x] ∘ g =
        Sum.elim (Subtype.val : ↥(insert t Q) → M) ![x] := by
      funext a
      cases a with
      | inl a =>
        by_cases ha : a.val ∈ Q
        · simp [g, ha]
        · have hat : a.val = t := (Set.mem_insert_iff.mp a.property).resolve_right ha
          have htQ : t ∉ Q := by simpa only [hat] using ha
          simp [g, hat, htQ]
      | inr i => fin_cases i; rfl
    rw [he]
    have hm := congrArg (fun U : Set (Fin 1 → M) => ![x] ∈ U) hφ
    exact (Iff.of_eq hm).symm
  refine ⟨R, ?_, Set.ext hreal⟩
  change Q.Definable L {z : Fin 2 → M | (z 0, z 1) ∈ R}
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨ψ, ?_⟩
  ext z
  have hz : (![z 0, z 1] : Fin 2 → M) = z := by
    funext i
    fin_cases i <;> rfl
  simp only [R, Set.mem_ofPred_eq, hz]

/-- A definable function sends algebraic points to algebraic points. -/
theorem IsAlgebraicPoint.map {t : M} (ht : IsAlgebraicPoint L Q t)
    {f : M → M} (hf : Q.DefinableFun L (fun z : Fin 1 → M => f (z 0))) :
    IsAlgebraicPoint L Q (f t) := by
  obtain ⟨S, hS, hfinite, ht⟩ := ht
  have hmap : Q.DefinableMap L (fun z : Fin 1 → M => ![f (z 0)]) := by
    intro i
    fin_cases i
    exact hf
  have hd := definable_image hS hmap
  have he : (fun z : Fin 1 → M => ![f (z 0)]) '' {z | z 0 ∈ S} =
      {z : Fin 1 → M | z 0 ∈ f '' S} := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a 0, ha, rfl⟩
    · rintro ⟨a, ha, haz⟩
      refine ⟨![a], ha, ?_⟩
      funext i
      fin_cases i
      exact haz
  have hd' : Q.Definable₁ L (f '' S) := by
    change Q.Definable L {z : Fin 1 → M | z 0 ∈ f '' S}
    rw [← he]
    exact hd
  exact ⟨f '' S, hd', hfinite.image f, Set.mem_image_of_mem f ht⟩

end IntegrationInACVF.Section3.DefinableFamilies
