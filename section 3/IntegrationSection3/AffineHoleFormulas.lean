module

public import IntegrationSection3.ImaginaryTupleFormulas

@[expose] public section

/-! Intrinsic finite affine-hole transport through all interpreted codes. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.AffineHoleFormulas

open ImaginaryTupleFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

/-- Add images of every ordered pair of distinct old holes, through each
of finitely many real point relations. The proper-parent guard applies
even to parents outside the radius class used in the construction. -/
def expansion (U : J → Set M) (D : Set J) (R : J → J → Prop)
    {N : ℕ} (A : Fin (N+1) → Set (Fin 3 → M)) (h p k : J) : Prop :=
  h ∈ D ∧ k ∈ D ∧ U k ⊂ U p ∧ ∃ l : J,
    R l p ∧ l ∈ D ∧ h ≠ l ∧ ∃ n : Fin (N+1), ∃ x : Fin 3 → M,
      (∀ i, x i ∈ U ((![h,l,k] : Fin 3 → J) i)) ∧ x ∈ A n

theorem expansion_definable (hp : B.real.Definable L p.codes)
    (hq : q.IsDefinable L B.real) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {D : Set J} (hD : ImaginaryBaseFamilies.Family (L := L) p B q D)
    {R : J → J → Prop}
    (hR : Predicate (L := L) p B q (fun a : Fin 2 → J => R (a 0) (a 1)))
    {N : ℕ} {A : Fin (N+1) → Set (Fin 3 → M)}
    (hA : ∀ n, OverBase (L := L) p B (A n)) :
    Predicate (L := L) p B q (fun a : Fin 3 → J =>
      expansion U D R A (a 0) (a 1) (a 2)) := by
  let S := Fin 3 ⊕ Fin 1
  have hdh := coordinate_mem hp hq.1 hD (Sum.inl (0 : Fin 3) : S)
  have hdk := coordinate_mem hp hq.1 hD (Sum.inl (2 : Fin 3) : S)
  have hdl := coordinate_mem hp hq.1 hD (Sum.inr (0 : Fin 1) : S)
  have hs := ImaginaryTupleFormulas.reindex hp hq.1 (strict_subset hp hq.1 hU)
    (![Sum.inl 2,Sum.inl 1] : Fin 2 → S)
  have hr := ImaginaryTupleFormulas.reindex hp hq.1 hR
    (![Sum.inr 0,Sum.inl 1] : Fin 2 → S)
  have hne := ImaginaryTupleFormulas.neg hp hq.1
    (coordinate_eq hp hq (Sum.inl 0 : S) (Sum.inr 0 : S))
  have ha := ImaginaryTupleFormulas.reindex hp hq.1
    (ImaginaryTupleFormulas.exists_finite hp (fun n =>
      exists_points hp hq.1 hU (hA n)))
      (![Sum.inl 0,Sum.inr 0,Sum.inl 2] : Fin 3 → S)
  have hall := inter hp hdh (inter hp hdk (inter hp hs
    (inter hp hr (inter hp hdl (inter hp hne ha)))))
  have hex := ImaginaryTupleFormulas.exists_block hall
  unfold Predicate at hex ⊢
  convert hex using 1
  congr 1
  ext a
  have htuple (b : Fin 1 → J) : Sum.elim a b ∘
      (![Sum.inl 0,Sum.inr 0,Sum.inl 2] : Fin 3 → S) = ![a 0,b 0,a 2] := by
    funext i
    fin_cases i <;> rfl
  simp only [Set.mem_ofPred_eq]
  simp_rw [htuple]
  change expansion U D R A (a 0) (a 1) (a 2) ↔
    ∃ b : Fin 1 → J, a 0 ∈ D ∧ a 2 ∈ D ∧ U (a 2) ⊂ U (a 1) ∧
      R (b 0) (a 1) ∧ b 0 ∈ D ∧ a 0 ≠ b 0 ∧
        ∃ n : Fin (N+1), ∃ x : Fin 3 → M,
          (∀ i, x i ∈ U ((![a 0,b 0,a 2] : Fin 3 → J) i)) ∧ x ∈ A n
  constructor
  · rintro ⟨hh,hk,hkp,l,hl,hlD,hne,n,x,hx,hA⟩
    exact ⟨![l],hh,hk,hkp,hl,hlD,hne,n,x,hx,hA⟩
  · rintro ⟨b,hh,hk,hkp,hl,hlD,hne,n,x,hx,hA⟩
    exact ⟨hh,hk,hkp,b 0,hl,hlD,hne,n,x,hx,hA⟩

end IntegrationInACVF.Section3.AffineHoleFormulas
