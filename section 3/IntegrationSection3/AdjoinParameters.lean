module

public import IntegrationSection3.ImaginaryBaseFamilies

@[expose] public section

/-! Adjoining an imaginary name agrees with a full invariant family over
the original interpreted base. This is a parameter-promotion theorem. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryParameters

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁

def Base.adjoin {M : Type w} {I : Type w'} (B : Base M I) (i : I) : Base M I :=
  ⟨B.real,insert i B.imaginary⟩

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} [Finite κ]
variable {p : Presentation M I κ} {B : Base M I}

theorem OverBase.adjoin_iff {υ : Type w₁} [Finite υ]
    (hp : p.IsDefinable L B.real) (i : I) (A : Set (υ → M)) :
    OverBase (L := L) p (B.adjoin i) A ↔
      ∃ R : I → Set (υ → M), OverBase (L := L) p B (vectorPullback p R) ∧ R i = A := by
  classical
  constructor
  · rintro ⟨F,hF,R,hR,he⟩
    let G := F.erase i
    let a : G ⊕ Unit → I := Sum.elim Subtype.val (fun _ => i)
    let f : F → G ⊕ Unit := fun j =>
      if h : j.val = i then Sum.inr ()
      else Sum.inl ⟨j.val,Finset.mem_erase.mpr ⟨h,j.property⟩⟩
    have hfa : a ∘ f = (Subtype.val : F → I) := by
      funext j
      by_cases h : j.val = i
      · simpa only [Function.comp_apply,a,f,dite_eq_left h,Sum.elim_inr] using h.symm
      · simp only [Function.comp_apply,a,f,dite_eq_right h,Sum.elim_inl]
    have hA : WithTuple (L := L) p B.real a A :=
      WithTuple.reindex ⟨R,hR,he⟩ hp.1 f hfa
    obtain ⟨S,hS,hSa⟩ := hA
    let C : I → Set (υ → M) :=
      fun j => S (Sum.elim (Subtype.val : G → I) (fun _ : Unit => j))
    refine ⟨C,?_,hSa⟩
    refine ⟨G,?_,(fun b => vectorPullback p
      (fun j => S (Sum.elim b (fun _ : Unit => j)))),?_,rfl⟩
    · intro j hj
      have hji := Finset.mem_erase.mp hj
      exact (hF j hji.2).resolve_left hji.1
    · let idx : ((G ⊕ Unit) × κ) ⊕ υ → (G × κ) ⊕ (κ ⊕ υ) :=
        Sum.elim (fun (j,c) => match j with
          | Sum.inl g => Sum.inl (g,c)
          | Sum.inr _ => Sum.inr (Sum.inl c))
          (fun v => Sum.inr (Sum.inr v))
      convert hS.preimage_comp idx using 1
      ext z
      have hout : (z ∘ idx) ∘ Sum.inr = (z ∘ Sum.inr) ∘ Sum.inr := by
        funext v
        rfl
      have hdecode (h : (z ∘ idx) ∘ Sum.inl ∈ (tuplePresentation p (G ⊕ Unit)).codes)
          (hb : z ∘ Sum.inl ∈ (tuplePresentation p G).codes)
          (hq : (z ∘ Sum.inr) ∘ Sum.inl ∈ p.codes) :
          (tuplePresentation p (G ⊕ Unit)).decode ⟨(z ∘ idx) ∘ Sum.inl,h⟩ =
            Sum.elim ((tuplePresentation p G).decode ⟨z ∘ Sum.inl,hb⟩)
              (fun _ : Unit => p.decode ⟨(z ∘ Sum.inr) ∘ Sum.inl,hq⟩) := by
        funext j
        cases j <;> rfl
      constructor
      · rintro ⟨hb,hq,hz⟩
        let h : (z ∘ idx) ∘ Sum.inl ∈ (tuplePresentation p (G ⊕ Unit)).codes :=
          fun j => by cases j with
            | inl g => exact hb g
            | inr _ => exact hq
        refine ⟨h,?_⟩
        change ((z ∘ idx) ∘ Sum.inr) ∈ S ((tuplePresentation p (G ⊕ Unit)).decode ⟨_,h⟩)
        rw [hout,hdecode h hb hq]
        exact hz
      · rintro ⟨h,hz⟩
        have hb : z ∘ Sum.inl ∈ (tuplePresentation p G).codes := fun g => h (Sum.inl g)
        have hq : (z ∘ Sum.inr) ∘ Sum.inl ∈ p.codes := h (Sum.inr ())
        change ((z ∘ idx) ∘ Sum.inr) ∈ S ((tuplePresentation p (G ⊕ Unit)).decode ⟨_,h⟩) at hz
        rw [hout,hdecode h hb hq] at hz
        exact ⟨hb,hq,hz⟩
  · rintro ⟨R,hR,he⟩
    have hRm : OverBase (L := L) p (B.adjoin i) (vectorPullback p R) :=
      hR.mono Set.Subset.rfl (Set.subset_insert i B.imaginary)
    have hn : OverBase (L := L) p (B.adjoin i) (p.pullback {i}) :=
      OverBase.named_singleton (B := B.adjoin i) hp (Set.mem_insert i B.imaginary)
    have hi := hRm.inter (hn.preimage_comp (Sum.inl : κ → κ ⊕ υ)) hp.1
    have hd := (hi.preimage_comp (Sum.swap : κ ⊕ υ → υ ⊕ κ)).exists_block
    convert hd using 1
    ext z
    constructor
    · intro hz
      obtain ⟨q,hq⟩ := p.onto i
      refine ⟨q.val,⟨q.property,?_⟩,q.property,hq⟩
      change z ∈ R (p.decode q)
      rw [hq,he]
      exact hz
    · rintro ⟨q,⟨hq,hz⟩,_,hq'⟩
      change q ∈ p.codes at hq
      change p.decode ⟨q,hq⟩ = i at hq'
      change z ∈ R (p.decode ⟨q,hq⟩) at hz
      rw [hq',he] at hz
      exact hz

theorem with_iff_over_adjoin (hp : p.IsDefinable L B.real) (i : I) (A : Set M) :
    ImaginaryBaseFamilies.With (L := L) p B p i A ↔
      OverBase (L := L) p (B.adjoin i) {z : Fin 1 → M | z 0 ∈ A} := by
  constructor
  · rintro ⟨C,hC,he⟩
    apply (OverBase.adjoin_iff hp i _).mpr
    refine ⟨(fun j => {z : Fin 1 → M | z 0 ∈ C j}),hC,?_⟩
    change {z : Fin 1 → M | z 0 ∈ C i} = {z | z 0 ∈ A}
    rw [he]
  · intro hA
    obtain ⟨R,hR,he⟩ := (OverBase.adjoin_iff hp i _).mp hA
    let C : I → Set M := fun j => {x | ![x] ∈ R j}
    have hC : ImaginaryBaseFamilies.Relation (L := L) p B p C := by
      change OverBase (L := L) p B (p.relationPullback C)
      convert hR using 1
      ext z
      have hz : z ∘ Sum.inr = ![z (.inr 0)] := by
        funext j; fin_cases j; rfl
      change (∃ h : z ∘ Sum.inl ∈ p.codes,
        ![z (.inr 0)] ∈ R (p.decode ⟨z ∘ Sum.inl,h⟩)) ↔
          (∃ h : z ∘ Sum.inl ∈ p.codes,
            z ∘ Sum.inr ∈ R (p.decode ⟨z ∘ Sum.inl,h⟩))
      rw [hz]
    refine ⟨C,hC,?_⟩
    ext x
    change ![x] ∈ R i ↔ x ∈ A
    rw [he]
    rfl

def IsAtomicOver (p : Presentation M I κ) (B : Base M I) (A : Set M) : Prop :=
  OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A} ∧
    ImaginaryBaseFamilies.CompleteType (L := L) p B A

theorem atomicWith_iff_atomic_adjoin (hp : p.IsDefinable L B.real) (i : I) (A : Set M) :
    ImaginaryBaseFamilies.AtomicWith (L := L) p B p i A ↔
      IsAtomicOver (L := L) p (B.adjoin i) A := by
  constructor
  · rintro ⟨hA,hall⟩
    exact ⟨(with_iff_over_adjoin hp i A).mp hA,
      fun S hS => hall S ((with_iff_over_adjoin hp i S).mpr hS)⟩
  · rintro ⟨hA,hall⟩
    exact ⟨(with_iff_over_adjoin hp i A).mpr hA,
      fun S hS => hall S ((with_iff_over_adjoin hp i S).mp hS)⟩

end IntegrationInACVF.Section3.ImaginaryParameters
