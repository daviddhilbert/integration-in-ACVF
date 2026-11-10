module

public import IntegrationSection3.ImaginaryFamilies

@[expose] public section

/-!
# Finite support in an arbitrary interpreted parameter base

This is the full-preimage convention of the predecessor's GammaParameters,
for an arbitrary already presented quotient. The base stores imaginary
elements, never selected real representatives. Specialization adjoins a
finite set of real codes only inside its conclusion; it is not used as the
definition of definability over the original base.
-/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3.ImaginaryParameters

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂ w₃

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}

def tupleCodes (p : Presentation M I κ) (θ : Type w₁) : Set (θ × κ → M) :=
  {a | ∀ j, (fun c => a (j,c)) ∈ p.codes}

noncomputable def tuplePresentation (p : Presentation M I κ) (θ : Type w₁) :
    Presentation M (θ → I) (θ × κ) where
  codes := tupleCodes p θ
  decode q j := p.decode ⟨(fun c => q.val (j,c)),q.property j⟩
  onto := by
    intro a
    choose q hq using fun j => p.onto (a j)
    exact ⟨⟨fun (j,c) => (q j).val c,fun j => (q j).property⟩,funext hq⟩

/-- Full guarded preimage of a relation with a finite tuple of real outputs. -/
def vectorPullback (p : Presentation M I κ) {υ : Type w₂}
    (R : I → Set (υ → M)) : Set (κ ⊕ υ → M) :=
  {z | ∃ hz : z ∘ Sum.inl ∈ p.codes,
    z ∘ Sum.inr ∈ R (p.decode ⟨z ∘ Sum.inl,hz⟩)}

def WithTuple (p : Presentation M I κ) (Q : Set M) {θ : Type w₁} {υ : Type w₂}
    (a : θ → I) (A : Set (υ → M)) : Prop :=
  ∃ R : (θ → I) → Set (υ → M),
    Q.Definable L (vectorPullback (tuplePresentation p θ) R) ∧ R a = A

structure Base (M : Type w) (I : Type w') where
  real : Set M
  imaginary : Set I

/-- A formula uses a finite subset of the named imaginary elements. Its
relation remains invariant on every code of each of those elements. -/
def OverBase (p : Presentation M I κ) (B : Base M I) {υ : Type w₂}
    (A : Set (υ → M)) : Prop :=
  ∃ F : Finset I, (∀ i ∈ F, i ∈ B.imaginary) ∧
    WithTuple (L := L) p B.real (Subtype.val : F → I) A

variable [Finite κ] {p : Presentation M I κ} {Q : Set M}

omit [Finite κ] in
theorem tupleCodes_definable (hp : Q.Definable L p.codes) (θ : Type w₁) [Finite θ] :
    Q.Definable L (tupleCodes p θ) := by
  change Q.Definable L {a : θ × κ → M | ∀ j, (fun c => a (j,c)) ∈ p.codes}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite fun j => hp.preimage_comp (fun c => (j,c))

/-- Specialization names a code only at this proof step. The code remains
visible in the enlarged real base of the conclusion. -/
theorem vector_specialize {υ : Type w₂} [Finite υ] {R : I → Set (υ → M)}
    (hR : Q.Definable L (vectorPullback p R)) (i : I) :
    ∃ q : p.codes, p.decode q = i ∧ (Q ∪ Set.range q.val).Definable L (R i) := by
  obtain ⟨q,hq⟩ := p.onto i
  refine ⟨q,hq,?_⟩
  have hm := hR.mono (Set.subset_union_left : Q ⊆ Q ∪ Set.range q.val)
  have hf : (Q ∪ Set.range q.val).DefinableMap L
      (fun z : υ → M => Sum.elim q.val z) := by
    intro j
    cases j with
    | inl c => exact L.definableFun_const υ (Or.inr ⟨c,rfl⟩)
    | inr j => exact Set.DefinableFun.proj L
  convert hm.preimage_map hf using 1
  ext z
  change z ∈ R i ↔ ∃ h : q.val ∈ p.codes, z ∈ R (p.decode ⟨q.val,h⟩)
  rw [← hq]
  exact ⟨fun h => ⟨q.property,h⟩,fun ⟨_,h⟩ => h⟩

theorem WithTuple.specialize {θ : Type w₁} [Finite θ] {υ : Type w₂} [Finite υ]
    {a : θ → I} {A : Set (υ → M)} (hA : WithTuple (L := L) p Q a A) :
    ∃ F : Set M, F.Finite ∧ (Q ∪ F).Definable L A := by
  obtain ⟨R,hR,rfl⟩ := hA
  obtain ⟨q,_,hq⟩ := vector_specialize hR a
  exact ⟨Set.range q.val,Set.finite_range q.val,hq⟩

theorem OverBase.specialize {B : Base M I} {υ : Type w₂} [Finite υ]
    {A : Set (υ → M)} (hA : OverBase (L := L) p B A) :
    ∃ F : Set M, F.Finite ∧ (B.real ∪ F).Definable L A := by
  obtain ⟨_,_,hA⟩ := hA
  exact hA.specialize

omit [Finite κ] in
theorem WithTuple.mono {θ : Type w₁} {υ : Type w₂} {a : θ → I}
    {A : Set (υ → M)} {Q' : Set M} (hA : WithTuple (L := L) p Q a A)
    (hQ : Q ⊆ Q') : WithTuple (L := L) p Q' a A := by
  obtain ⟨R,hR,he⟩ := hA
  exact ⟨R,hR.mono hQ,he⟩

omit [Finite κ] in
theorem OverBase.mono {B B' : Base M I} {υ : Type w₂} {A : Set (υ → M)}
    (hA : OverBase (L := L) p B A) (hreal : B.real ⊆ B'.real)
    (himag : B.imaginary ⊆ B'.imaginary) : OverBase (L := L) p B' A := by
  obtain ⟨F,hF,hA⟩ := hA
  exact ⟨F,fun i hi => himag (hF i hi),hA.mono hreal⟩

omit [Finite κ] in
theorem WithTuple.reindex {θ θ' : Type w₁} [Finite θ] [Finite θ']
    {υ : Type w₂} [Finite υ] {a : θ → I} {b : θ' → I} {A : Set (υ → M)}
    (hA : WithTuple (L := L) p Q a A) (hp : Q.Definable L p.codes)
    (f : θ → θ') (hba : b ∘ f = a) : WithTuple (L := L) p Q b A := by
  obtain ⟨R,hR,he⟩ := hA
  let S : (θ' → I) → Set (υ → M) := fun c => R (c ∘ f)
  refine ⟨S,?_,?_⟩
  · have hd := (tupleCodes_definable hp θ').preimage_comp
      (Sum.inl : θ' × κ → (θ' × κ) ⊕ υ)
    have hr := hR.preimage_comp (Sum.map (fun (j,c) => (f j,c)) id)
    convert hd.inter hr using 1
    ext z
    constructor
    · rintro ⟨hz,hzR⟩
      exact ⟨hz,fun j => hz (f j),hzR⟩
    · rintro ⟨hz,_,hzR⟩
      exact ⟨hz,hzR⟩
  · change R (b ∘ f) = A
    rw [hba]
    exact he

omit [Finite κ] in
theorem WithTuple.inter {θ : Type w₁} [Finite θ] {υ : Type w₂} [Finite υ]
    {a : θ → I} {A C : Set (υ → M)}
    (hA : WithTuple (L := L) p Q a A) (hC : WithTuple (L := L) p Q a C) :
    WithTuple (L := L) p Q a (A ∩ C) := by
  obtain ⟨R,hR,rfl⟩ := hA
  obtain ⟨S,hS,rfl⟩ := hC
  refine ⟨fun i => R i ∩ S i,?_,rfl⟩
  convert hR.inter hS using 1
  ext z
  exact ⟨fun ⟨hz,hr,hs⟩ => ⟨⟨hz,hr⟩,hz,hs⟩,
    fun ⟨⟨hz,hr⟩,_,hs⟩ => ⟨hz,hr,hs⟩⟩

omit [Finite κ] in
theorem WithTuple.compl {θ : Type w₁} [Finite θ] {υ : Type w₂} [Finite υ]
    {a : θ → I} {A : Set (υ → M)}
    (hA : WithTuple (L := L) p Q a A) (hp : Q.Definable L p.codes) :
    WithTuple (L := L) p Q a Aᶜ := by
  obtain ⟨R,hR,rfl⟩ := hA
  refine ⟨fun i => (R i)ᶜ,?_,rfl⟩
  have hd := (tupleCodes_definable hp θ).preimage_comp
    (Sum.inl : θ × κ → (θ × κ) ⊕ υ)
  convert hd.inter hR.compl using 1
  ext z
  exact ⟨fun ⟨hz,hn⟩ => ⟨hz,fun ⟨_,h⟩ => hn h⟩,
    fun ⟨hz,hn⟩ => ⟨hz,fun h => hn ⟨hz,h⟩⟩⟩

omit [Finite κ] in
theorem OverBase.of_real {B : Base M I} {υ : Type w₂} [Finite υ]
    {A : Set (υ → M)} (hA : B.real.Definable L A) : OverBase (L := L) p B A := by
  classical
  refine ⟨∅,by simp,fun _ => A,?_,rfl⟩
  convert hA.preimage_comp (Sum.inr : υ → ((∅ : Finset I) × κ) ⊕ υ) using 1
  ext z
  exact ⟨fun ⟨_,h⟩ => h,
    fun h => ⟨(fun j => (Finset.notMem_empty j.val j.property).elim),h⟩⟩

omit [Finite κ] in
theorem OverBase.inter {B : Base M I} {υ : Type w₂} [Finite υ] {A C : Set (υ → M)}
    (hA : OverBase (L := L) p B A) (hC : OverBase (L := L) p B C)
    (hp : B.real.Definable L p.codes) : OverBase (L := L) p B (A ∩ C) := by
  classical
  obtain ⟨F,hF,hA⟩ := hA
  obtain ⟨G,hG,hC⟩ := hC
  refine ⟨F ∪ G,?_,?_⟩
  · intro i hi
    exact (Finset.mem_union.mp hi).elim (hF i) (hG i)
  · have ha := hA.reindex (b := (Subtype.val : ↥(F ∪ G) → I)) hp (fun j : F => (⟨j.val,Finset.mem_union_left G j.property⟩ : ↥(F ∪ G))) rfl
    have hc := hC.reindex (b := (Subtype.val : ↥(F ∪ G) → I)) hp (fun j : G => (⟨j.val,Finset.mem_union_right F j.property⟩ : ↥(F ∪ G))) rfl
    exact ha.inter hc

omit [Finite κ] in
theorem OverBase.compl {B : Base M I} {υ : Type w₂} [Finite υ] {A : Set (υ → M)}
    (hA : OverBase (L := L) p B A) (hp : B.real.Definable L p.codes) :
    OverBase (L := L) p B Aᶜ := by
  obtain ⟨F,hF,hA⟩ := hA
  exact ⟨F,hF,hA.compl hp⟩

omit [Finite κ] in
theorem WithTuple.preimage_comp {θ : Type w₁} {υ : Type w₂} {β : Type w₃}
    {a : θ → I} {A : Set (υ → M)}
    (hA : WithTuple (L := L) p Q a A) (f : υ → β) :
    WithTuple (L := L) p Q a ((fun z : β → M => z ∘ f) ⁻¹' A) := by
  obtain ⟨R,hR,rfl⟩ := hA
  refine ⟨fun i => (fun z : β → M => z ∘ f) ⁻¹' R i,?_,rfl⟩
  convert hR.preimage_comp (Sum.map id f) using 1
  ext z
  simp only [vectorPullback, Set.mem_ofPred_eq, Set.mem_preimage,
    Function.comp_def, Sum.map_inl, Sum.map_inr, id_eq]

omit [Finite κ] in
theorem OverBase.preimage_comp {B : Base M I} {υ : Type w₂} {β : Type w₃}
    {A : Set (υ → M)} (hA : OverBase (L := L) p B A) (f : υ → β) :
    OverBase (L := L) p B ((fun z : β → M => z ∘ f) ⁻¹' A) := by
  obtain ⟨F,hF,hA⟩ := hA
  exact ⟨F,hF,hA.preimage_comp f⟩

omit [Finite κ] in
theorem WithTuple.exists_block {θ : Type w₁} {υ : Type w₂} {β : Type w₃} [Finite β]
    {a : θ → I} {A : Set (υ ⊕ β → M)} (hA : WithTuple (L := L) p Q a A) :
    WithTuple (L := L) p Q a {z | ∃ b : β → M, Sum.elim z b ∈ A} := by
  obtain ⟨R,hR,rfl⟩ := hA
  refine ⟨fun i => {z | ∃ b : β → M, Sum.elim z b ∈ R i},?_,rfl⟩
  let f : (θ × κ) ⊕ (υ ⊕ β) → ((θ × κ) ⊕ υ) ⊕ β :=
    Sum.elim (fun c => .inl (.inl c))
      (Sum.elim (fun v => .inl (.inr v)) Sum.inr)
  have h := (hR.preimage_comp f).exists_of_finite
  convert h using 1
  ext z
  have hreal (b : β → M) :
      (Sum.elim z b ∘ f) ∘ Sum.inr = Sum.elim (z ∘ Sum.inr) b := by
    funext j
    cases j <;> rfl
  constructor
  · rintro ⟨hz,b,hb⟩
    refine ⟨b,hz,?_⟩
    change ((Sum.elim z b ∘ f) ∘ Sum.inr) ∈ _
    rw [hreal]
    exact hb
  · rintro ⟨b,hz,hb⟩
    refine ⟨hz,b,?_⟩
    change ((Sum.elim z b ∘ f) ∘ Sum.inr) ∈ _ at hb
    rw [hreal] at hb
    exact hb

omit [Finite κ] in
theorem OverBase.exists_block {B : Base M I} {υ : Type w₂} {β : Type w₃} [Finite β]
    {A : Set (υ ⊕ β → M)} (hA : OverBase (L := L) p B A) :
    OverBase (L := L) p B {z | ∃ b : β → M, Sum.elim z b ∈ A} := by
  obtain ⟨F,hF,hA⟩ := hA
  exact ⟨F,hF,hA.exists_block⟩

omit [Finite κ] in
theorem WithTuple.preimage_map {θ : Type w₁} [Finite θ] [Finite κ]
    {υ : Type w₂} [Finite υ] {β : Type w₃} [Finite β]
    {a : θ → I} {A : Set (υ → M)} {F : (β → M) → (υ → M)}
    (hA : WithTuple (L := L) p Q a A) (hF : Q.DefinableMap L F) :
    WithTuple (L := L) p Q a (F ⁻¹' A) := by
  obtain ⟨R,hR,rfl⟩ := hA
  let G : ((θ × κ) ⊕ β → M) → ((θ × κ) ⊕ υ → M) :=
    fun z => Sum.elim (z ∘ Sum.inl) (F (z ∘ Sum.inr))
  have hG : Q.DefinableMap L G := by
    intro j
    cases j with
    | inl c => exact Set.DefinableFun.proj L
    | inr j => exact (hF j).comp (fun _ => Set.DefinableFun.proj L)
  refine ⟨fun i => F ⁻¹' R i,?_,rfl⟩
  convert hR.preimage_map hG using 1
  ext z
  rfl

theorem OverBase.preimage_map {B : Base M I} {υ : Type w₂} [Finite υ] {β : Type w₃} [Finite β]
    {A : Set (υ → M)} {F : (β → M) → (υ → M)}
    (hA : OverBase (L := L) p B A) (hF : B.real.DefinableMap L F) :
    OverBase (L := L) p B (F ⁻¹' A) := by
  obtain ⟨S,hS,hA⟩ := hA
  exact ⟨S,hS,hA.preimage_map hF⟩

theorem OverBase.empty_iff_real {B : Base M I} {υ : Type w₂} [Finite υ]
    {A : Set (υ → M)} (hB : B.imaginary = ∅) :
    OverBase (L := L) p B A ↔ B.real.Definable L A := by
  classical
  constructor
  · rintro ⟨F,hF,R,hR,he⟩
    have hFe : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Set.notMem_empty i (hB ▸ hF i hi)
    subst F
    obtain ⟨q,_,hq⟩ := vector_specialize hR (Subtype.val : (∅ : Finset I) → I)
    have hrange : Set.range q.val = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨c,_⟩
      exact Finset.notMem_empty c.1.val c.1.property
    simpa only [hrange,Set.union_empty,he] using hq
  · exact OverBase.of_real

theorem OverBase.forall_block {B : Base M I} {υ : Type w₂} [Finite υ]
    {β : Type w₃} [Finite β] {A : Set (υ ⊕ β → M)}
    (hA : OverBase (L := L) p B A) (hp : B.real.Definable L p.codes) :
    OverBase (L := L) p B {z | ∀ b : β → M, Sum.elim z b ∈ A} := by
  classical
  have h := ((hA.compl hp).exists_block).compl hp
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_exists,not_not]

/-- A named imaginary has a definable singleton over the base naming it;
its full real preimage is used, rather than a selected representative. -/
theorem OverBase.named_singleton {B : Base M I} (hp : p.IsDefinable L B.real)
    {i : I} (hi : i ∈ B.imaginary) : OverBase (L := L) p B (p.pullback {i}) := by
  classical
  let F : Finset I := {i}
  let j : F := ⟨i,Finset.mem_singleton_self i⟩
  let R : (F → I) → Set (κ → M) := fun a => p.pullback {a j}
  refine ⟨F,?_,R,?_,rfl⟩
  · intro c hc
    exact (Finset.mem_singleton.mp hc) ▸ hi
  · have hd := (tupleCodes_definable hp.1 F).preimage_comp
      (Sum.inl : F × κ → (F × κ) ⊕ κ)
    have he := hp.2.preimage_comp
      (Sum.elim Sum.inr (fun c => (Sum.inl (j,c) : (F × κ) ⊕ κ)))
    convert hd.inter he using 1
    ext z
    exact ⟨fun ⟨hz,hout,he⟩ => ⟨hz,hout,hz j,he⟩,
      fun ⟨hz,hout,_,he⟩ => ⟨hz,hout,he⟩⟩

/-- C-minimality can be used after specialization without changing the
definability assertion over the original interpreted base. -/
theorem finite_ball_support {B : Base M I} {D : Set M} {balls : Set (Set M)}
    (hcm : ∀ Q' : Set M, CMinimalOn L Q' D balls) {S : Set M}
    (hS : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S}) (hsub : S ⊆ D) :
    HasFiniteBallSupport balls S := by
  obtain ⟨F,_,hF⟩ := hS.specialize
  exact hcm (B.real ∪ F) S hF hsub

end IntegrationInACVF.Section3.ImaginaryParameters
