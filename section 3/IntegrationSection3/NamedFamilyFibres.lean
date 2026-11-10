module

public import IntegrationSection3.ImaginaryTupleFormulas

@[expose] public section

/-! Recover a definable imaginary name from its definable point set, and
specialize a joint graph at a same-base definable name through all codes. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.ImaginaryTupleFormulas

namespace IntegrationInACVF.Section3.NamedFamilyFibres

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

theorem equal_family (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {A : Set M} (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A}) :
    ImaginaryBaseFamilies.Family (L := L) p B q {j | U j = A} := by
  have ha := hA.preimage_comp (Sum.inr : Fin 1 → η ⊕ Fin 1)
  have he := OverBase.forall_block (SupportFormulas.iff_definable hp hU ha) hp
  have hv := OverBase.of_real (p := p) (B := B) hq
  change OverBase (L := L) p B (q.pullback {j | U j = A})
  convert OverBase.inter hv he hp using 1
  ext c
  change (∃ hc : c ∈ q.codes, U (q.decode ⟨c,hc⟩) = A) ↔
    (c ∈ q.codes ∧ ∀ x : Fin 1 → M,
      (∃ hc : c ∈ q.codes, x 0 ∈ U (q.decode ⟨c,hc⟩)) ↔ x 0 ∈ A)
  constructor
  · rintro ⟨hc,he⟩
    refine ⟨hc,fun x => ?_⟩
    constructor
    · rintro ⟨_,hx⟩
      exact he ▸ hx
    · intro hx
      exact ⟨hc,he.symm ▸ hx⟩
  · rintro ⟨hc,he⟩
    refine ⟨hc,Set.ext fun x => ?_⟩
    exact ⟨fun hx => (he ![x]).mp ⟨hc,hx⟩,
      fun hx => ((he ![x]).mpr hx).choose_spec⟩

theorem singleton_of_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U) (hinj : Function.Injective U)
    (j : J) (hj : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ U j}) :
    ImaginaryBaseFamilies.Family (L := L) p B q {j} := by
  have he : {i | U i = U j} = ({j} : Set J) := by
    ext i
    exact ⟨fun h => hinj h,fun h => congrArg U h⟩
  simpa only [he] using equal_family hp hq hU hj

omit [Finite η] in
theorem unary_family {P : J → Prop}
    (hP : Predicate (L := L) p B q (fun a : Fin 1 → J => P (a 0))) :
    ImaginaryBaseFamilies.Family (L := L) p B q {j | P j} := by
  unfold Predicate at hP
  have hd := hP.preimage_comp (fun a : Fin 1 × η => a.2)
  change OverBase (L := L) p B (q.pullback {j | P j})
  convert hd using 1
  ext c
  exact ⟨fun ⟨hc,h⟩ => ⟨(fun _ => hc),h⟩,fun ⟨hc,h⟩ => ⟨hc 0,h⟩⟩

theorem binary_fibre (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {P : J → J → Prop}
    (hP : Predicate (L := L) p B q (fun a : Fin 2 → J => P (a 0) (a 1)))
    (j : J) (hj : ImaginaryBaseFamilies.Family (L := L) p B q {j}) :
    ImaginaryBaseFamilies.Family (L := L) p B q {i | P i j} := by
  have hp' := ImaginaryTupleFormulas.reindex hp hq hP
    (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hj' := coordinate_mem hp hq hj (Sum.inr (0 : Fin 1) : Fin 1 ⊕ Fin 1)
  have hd := ImaginaryTupleFormulas.exists_block (ImaginaryTupleFormulas.inter hp hp' hj')
  have he : (fun a : Fin 1 → J => ∃ b : Fin 1 → J,
      P (a 0) (b 0) ∧ b 0 ∈ ({j} : Set J)) = (fun a => P (a 0) j) := by
    funext a
    apply propext
    exact ⟨fun ⟨b,hb,hbj⟩ => (show b 0 = j from hbj) ▸ hb,
      fun h => ⟨![j],h,rfl⟩⟩
  apply unary_family
  change Predicate (L := L) p B q
    (fun a : Fin 1 → J => ∃ b : Fin 1 → J, P (a 0) (b 0) ∧ b 0 ∈ ({j} : Set J)) at hd
  rwa [he] at hd

end IntegrationInACVF.Section3.NamedFamilyFibres
