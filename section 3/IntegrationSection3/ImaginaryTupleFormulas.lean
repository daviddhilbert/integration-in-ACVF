module

public import IntegrationSection3.BallInclusionFormulas

@[expose] public section

/-! First-order tuple calculus through all codes of interpreted indices.
This is a formula construction on the original real structure and base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryTupleFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def Predicate {ι : Type*} (p : Presentation M I κ) (B : Base M I)
    (q : Presentation M J η) (P : (ι → J) → Prop) : Prop :=
  OverBase (L := L) p B ((tuplePresentation q ι).pullback {a | P a})

theorem inter {ι : Type*} [Finite ι] (hp : B.real.Definable L p.codes)
    {P Q : (ι → J) → Prop} (hP : Predicate (L := L) p B q P)
    (hQ : Predicate (L := L) p B q Q) :
    Predicate (L := L) p B q (fun a => P a ∧ Q a) :=
  ImaginaryBaseFamilies.Family.inter hp hP hQ

theorem neg {ι : Type*} [Finite ι] (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes)
    {P : (ι → J) → Prop} (hP : Predicate (L := L) p B q P) :
    Predicate (L := L) p B q (fun a => ¬ P a) :=
  RegionFormulas.family_compl hp (tupleCodes_definable hq ι) hP

theorem reindex {ι υ : Type*} [Finite ι] [Finite υ]
    (hp : B.real.Definable L p.codes) (hq : B.real.Definable L q.codes)
    {P : (ι → J) → Prop} (hP : Predicate (L := L) p B q P) (f : ι → υ) :
    Predicate (L := L) p B q (fun a => P (a ∘ f)) := by
  have hv := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq υ)
  have hr := hP.preimage_comp (fun x : ι × η => (f x.1,x.2))
  unfold Predicate
  convert OverBase.inter hv hr hp using 1
  ext c
  change (∃ hc : c ∈ tupleCodes q υ,
    P (fun i => q.decode ⟨(fun e => c (f i,e)),hc (f i)⟩)) ↔
    (c ∈ tupleCodes q υ ∧ ∃ hc : c ∘ (fun x : ι × η => (f x.1,x.2)) ∈ tupleCodes q ι,
      P (fun i => q.decode ⟨(fun e => c (f i,e)),hc i⟩))
  exact ⟨fun ⟨hc,h⟩ => ⟨hc,fun i => hc (f i),h⟩,
    fun ⟨hc,_,h⟩ => ⟨hc,h⟩⟩

theorem exists_finite {ι τ : Type*} [Finite ι] [Finite τ]
    (hp : B.real.Definable L p.codes)
    {P : τ → (ι → J) → Prop} (hP : ∀ t, Predicate (L := L) p B q (P t)) :
    Predicate (L := L) p B q (fun a => ∃ t, P t a) := by
  have hd := SupportFormulas.exists_finite hp hP
  unfold Predicate
  convert hd using 1
  ext c
  change (∃ hc : c ∈ tupleCodes q ι,
      ∃ t, P t ((tuplePresentation q ι).decode ⟨c,hc⟩)) ↔
    (∃ t, ∃ hc : c ∈ tupleCodes q ι,
      P t ((tuplePresentation q ι).decode ⟨c,hc⟩))
  exact ⟨fun ⟨hc,t,h⟩ => ⟨t,hc,h⟩,fun ⟨t,hc,h⟩ => ⟨hc,t,h⟩⟩

/-- Quantify an entire finite imaginary block using its full code domain.
No representative of the quantified tuple is added to the base. -/
theorem exists_block {ι υ : Type*} [Finite ι] [Finite υ]
    {P : (ι ⊕ υ → J) → Prop} (hP : Predicate (L := L) p B q P) :
    Predicate (L := L) p B q (fun a => ∃ b : υ → J, P (Sum.elim a b)) := by
  let π : (ι ⊕ υ) × η → (ι × η) ⊕ (υ × η) :=
    fun (i,e) => i.elim (fun j => .inl (j,e)) (fun j => .inr (j,e))
  have hd := OverBase.exists_block (hP.preimage_comp π)
  unfold Predicate
  convert hd using 1
  ext c
  constructor
  · rintro ⟨hc,b,hb⟩
    obtain ⟨d,hd⟩ := (tuplePresentation q υ).onto b
    have hv : Sum.elim c d.val ∘ π ∈ tupleCodes q (ι ⊕ υ) := by
      intro i
      cases i with
      | inl i => exact hc i
      | inr i => exact d.property i
    refine ⟨d.val,hv,?_⟩
    change P ((tuplePresentation q (ι ⊕ υ)).decode ⟨Sum.elim c d.val ∘ π,hv⟩)
    have he : (tuplePresentation q (ι ⊕ υ)).decode ⟨Sum.elim c d.val ∘ π,hv⟩ =
        Sum.elim ((tuplePresentation q ι).decode ⟨c,hc⟩) b := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact congrFun hd i
    rwa [he]
  · rintro ⟨d,hv,hh⟩
    have hc : c ∈ tupleCodes q ι := fun i => hv (.inl i)
    have hd : d ∈ tupleCodes q υ := fun i => hv (.inr i)
    refine ⟨hc,(tuplePresentation q υ).decode ⟨d,hd⟩,?_⟩
    have he : (tuplePresentation q (ι ⊕ υ)).decode ⟨Sum.elim c d ∘ π,hv⟩ =
        Sum.elim ((tuplePresentation q ι).decode ⟨c,hc⟩)
          ((tuplePresentation q υ).decode ⟨d,hd⟩) := by
      funext i
      cases i <;> rfl
    exact he ▸ hh

theorem coordinate_eq {ι : Type*} [Finite ι]
    (hp : B.real.Definable L p.codes) (hq : q.IsDefinable L B.real) (i j : ι) :
    Predicate (L := L) p B q (fun a => a i = a j) := by
  have hv := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq.1 ι)
  have he := (OverBase.of_real (p := p) (B := B) hq.2).preimage_comp
    (Sum.elim (fun e => (i,e)) (fun e => (j,e)))
  unfold Predicate
  convert OverBase.inter hv he hp using 1
  ext c
  exact ⟨fun ⟨hc,h⟩ => ⟨hc,hc i,hc j,h⟩,fun ⟨hc,_,_,h⟩ => ⟨hc,h⟩⟩

theorem coordinate_mem {ι : Type*} [Finite ι]
    (hp : B.real.Definable L p.codes) (hq : B.real.Definable L q.codes)
    {D : Set J} (hD : ImaginaryBaseFamilies.Family (L := L) p B q D) (i : ι) :
    Predicate (L := L) p B q (fun a => a i ∈ D) := by
  have hv := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq ι)
  have hd := hD.preimage_comp (fun e => (i,e))
  unfold Predicate
  convert OverBase.inter hv hd hp using 1
  ext c
  exact ⟨fun ⟨hc,h⟩ => ⟨hc,hc i,h⟩,fun ⟨hc,_,h⟩ => ⟨hc,h⟩⟩

theorem strict_subset (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U) :
    Predicate (L := L) p B q (fun a : Fin 2 → J => U (a 0) ⊂ U (a 1)) := by
  unfold Predicate
  convert RegionFormulas.strictSubsetCodes_definable hp hq hU using 1
  ext c
  exact ⟨fun ⟨hc,h⟩ => (RegionFormulas.mem_strictSubsetCodes_iff c hc).mpr h,
    fun h => ⟨h.1,(RegionFormulas.mem_strictSubsetCodes_iff c h.1).mp h⟩⟩

/-- Lift a real relation by existentially quantifying points in the indexed
sets. All membership tests retain the full presentation preimages. -/
theorem exists_points {ι : Type*} [Finite ι]
    (hp : B.real.Definable L p.codes) (hq : B.real.Definable L q.codes)
    {U : J → Set M} (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {R : Set (ι → M)} (hR : OverBase (L := L) p B R) :
    Predicate (L := L) p B q (fun a => ∃ x : ι → M,
      (∀ i, x i ∈ U (a i)) ∧ x ∈ R) := by
  let π (i : ι) : η ⊕ Fin 1 → (ι × η) ⊕ ι :=
    Sum.elim (fun e => .inl (i,e)) (fun _ => .inr i)
  have hm := OverBase.forall_finite (fun i => hU.preimage_comp (π i)) hp
  have hr := hR.preimage_comp (Sum.inr : ι → (ι × η) ⊕ ι)
  have hd := OverBase.exists_block (OverBase.inter hm hr hp)
  have hv := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq ι)
  unfold Predicate
  convert OverBase.inter hv hd hp using 1
  ext c
  have he (x : ι → M) (i : ι) :
      Sum.elim c x ∘ π i = Sum.elim (fun e => c (i,e)) ![x i] := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => fin_cases e; rfl
  change (∃ hc : c ∈ tupleCodes q ι, ∃ x : ι → M,
      (∀ i, x i ∈ U (q.decode ⟨(fun e => c (i,e)),hc i⟩)) ∧ x ∈ R) ↔
    (c ∈ tupleCodes q ι ∧ ∃ x : ι → M,
      (∀ i, Sum.elim c x ∘ π i ∈ q.relationPullback U) ∧ x ∈ R)
  simp only [he]
  constructor
  · rintro ⟨hc,x,hx,hr⟩
    exact ⟨hc,x,fun i => (q.mem_relationPullback U ⟨_,hc i⟩ _).mpr (hx i),hr⟩
  · rintro ⟨hc,x,hx,hr⟩
    exact ⟨hc,x,fun i => (q.mem_relationPullback U ⟨_,hc i⟩ _).mp (hx i),hr⟩

end IntegrationInACVF.Section3.ImaginaryTupleFormulas
