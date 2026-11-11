module

public import IntegrationSection3.LocallyFiniteRelations

@[expose] public section

/-! A first-order sentence for definable partial injective self-relations.
It names no function and is uniform in the graph formula and parameters. -/

open Set Classical FirstOrder FirstOrder.Language FirstOrder.Language.BoundedFormula

namespace IntegrationInACVF.Section3.DefinableInjectionSentence

variable {α ι : Type*}

def row {n : ℕ} (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) (a b : Fin n) :
    Language.ring.Formula (α ⊕ (Fin n × ι)) :=
  φ.relabel (Sum.map id (Sum.elim (fun i => (a,i)) (fun i => (b,i))))

noncomputable def equalRows [Finite ι] {n : ℕ} (a b : Fin n) :
    Language.ring.Formula (α ⊕ (Fin n × ι)) :=
  Formula.iInf (fun i : ι => (.var (.inl (.inr (a,i)))) =' (.var (.inl (.inr (b,i)))))

noncomputable def successor [Finite ι] (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) :
    Language.ring.Formula (α ⊕ (Fin 2 × ι)) :=
  Formula.iExs ι (φ.relabel (Sum.elim
    (fun a => .inl (.inl a))
    (Sum.elim (fun i => .inl (.inr (1,i))) (fun i => .inr i))))

noncomputable def predecessor [Finite ι] (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) :
    Language.ring.Formula (α ⊕ (Fin 2 × ι)) :=
  Formula.iExs ι (φ.relabel (Sum.elim
    (fun a => .inl (.inl a))
    (Sum.elim (fun i => .inr i) (fun i => .inl (.inr (0,i))))))

noncomputable def scheme [Finite ι] [Finite α]
    (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) : Language.ring.Sentence :=
  let rightUnique : Language.ring.Formula α := Formula.iAlls (Fin 3 × ι)
    ((row φ 0 1).imp ((row φ 0 2).imp (equalRows 1 2)))
  let leftUnique : Language.ring.Formula α := Formula.iAlls (Fin 3 × ι)
    ((row φ 0 2).imp ((row φ 1 2).imp (equalRows 0 1)))
  let next : Language.ring.Formula α := Formula.iAlls (Fin 2 × ι)
    ((row φ 0 1).imp (successor φ))
  let previous : Language.ring.Formula α := Formula.iAlls (Fin 2 × ι)
    ((row φ 0 1).imp (predecessor φ))
  Formula.iAlls α ((rightUnique.imp (leftUnique.imp (next.imp previous))).relabel Sum.inr)

section Semantics

variable {K : Type*} [Language.ring.Structure K]

theorem realize_row {n : ℕ} (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) (a b : Fin n)
    (v : α → K) (w : Fin n × ι → K) :
    (row φ a b).Realize (Sum.elim v w) ↔
      φ.Realize (Sum.elim v (Sum.elim (fun i => w (a,i)) (fun i => w (b,i)))) := by
  simp only [row,Formula.realize_relabel]
  apply iff_of_eq
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

theorem realize_equalRows [Finite ι] {n : ℕ} (a b : Fin n)
    (v : α → K) (w : Fin n × ι → K) :
    (equalRows (α := α) (ι := ι) a b).Realize (Sum.elim v w) ↔
      (fun i => w (a,i)) = (fun i => w (b,i)) := by
  simp only [equalRows,Formula.iInf,Formula.Realize,BoundedFormula.realize_iInf,
    BoundedFormula.realize_bdEqual,Term.realize_var,Sum.elim_inl,Sum.elim_inr]
  exact funext_iff.symm

theorem realize_successor [Finite ι] (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι)))
    (v : α → K) (w : Fin 2 × ι → K) :
    (successor φ).Realize (Sum.elim v w) ↔
      ∃ z : ι → K, φ.Realize (Sum.elim v (Sum.elim (fun i => w (1,i)) z)) := by
  simp only [successor,Formula.realize_iExs,Formula.realize_relabel]
  apply exists_congr
  intro z
  apply iff_of_eq
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

theorem realize_predecessor [Finite ι] (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι)))
    (v : α → K) (w : Fin 2 × ι → K) :
    (predecessor φ).Realize (Sum.elim v w) ↔
      ∃ z : ι → K, φ.Realize (Sum.elim v (Sum.elim z (fun i => w (0,i)))) := by
  simp only [predecessor,Formula.realize_iExs,Formula.realize_relabel]
  apply exists_congr
  intro z
  apply iff_of_eq
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

theorem realize_scheme [Finite ι] [Finite α]
    (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) :
    (K ⊨ scheme φ) ↔ ∀ v : α → K,
      (∀ w : Fin 3 × ι → K,
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (0,i)) (fun i => w (1,i)))) →
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (0,i)) (fun i => w (2,i)))) →
        (fun i => w (1,i)) = (fun i => w (2,i))) →
      (∀ w : Fin 3 × ι → K,
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (0,i)) (fun i => w (2,i)))) →
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (1,i)) (fun i => w (2,i)))) →
        (fun i => w (0,i)) = (fun i => w (1,i))) →
      (∀ w : Fin 2 × ι → K,
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (0,i)) (fun i => w (1,i)))) →
        ∃ z : ι → K, φ.Realize (Sum.elim v (Sum.elim (fun i => w (1,i)) z))) →
      ∀ w : Fin 2 × ι → K,
        φ.Realize (Sum.elim v (Sum.elim (fun i => w (0,i)) (fun i => w (1,i)))) →
        ∃ z : ι → K, φ.Realize (Sum.elim v (Sum.elim z (fun i => w (0,i)))) := by
  simp only [scheme,Sentence.Realize,Formula.realize_iAlls,Formula.realize_relabel,
    Formula.realize_imp,realize_row,realize_equalRows,realize_successor,realize_predecessor]
  rfl

end Semantics

end IntegrationInACVF.Section3.DefinableInjectionSentence
