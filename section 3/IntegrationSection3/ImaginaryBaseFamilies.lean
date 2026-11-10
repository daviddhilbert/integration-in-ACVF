module

public import IntegrationSection3.ImaginaryParameters

@[expose] public section

/-! Family arguments with an arbitrary finitely supported interpreted base.
The presentation of the parameter sort and that of the family index can
differ. In ACVF the former can combine Gamma and ball names. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryBaseFamilies

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable (p : Presentation M I κ) (B : Base M I) (q : Presentation M J η)

def Family (T : Set J) : Prop := OverBase (L := L) p B (q.pullback T)
def Relation (C : J → Set M) : Prop := OverBase (L := L) p B (q.relationPullback C)
def With (j : J) (A : Set M) : Prop := ∃ C, Relation (L := L) p B q C ∧ C j = A
def Algebraic (j : J) : Prop := ∃ T, Family (L := L) p B q T ∧ T.Finite ∧ j ∈ T
def AtomicWith (j : J) (A : Set M) : Prop :=
  With (L := L) p B q j A ∧
    ∀ S : Set M, With (L := L) p B q j S → A ⊆ S ∨ Disjoint A S
def CompleteType (A : Set M) : Prop :=
  ∀ S : Set M, OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S} →
    A ⊆ S ∨ Disjoint A S

variable {p B q} [Finite η]
variable (hp : B.real.Definable L p.codes)

include hp in
theorem Relation.inter {C P : J → Set M}
    (hC : Relation (L := L) p B q C) (hP : Relation (L := L) p B q P) :
    Relation (L := L) p B q (fun j => C j ∩ P j) := by
  change OverBase (L := L) p B (q.relationPullback (fun j => C j ∩ P j))
  convert OverBase.inter hC hP hp using 1
  ext z
  exact ⟨fun ⟨hz,hc,hp⟩ => ⟨⟨hz,hc⟩,hz,hp⟩,
    fun ⟨⟨hz,hc⟩,_,hp⟩ => ⟨hz,hc,hp⟩⟩

include hp in
theorem Relation.compl (hq : B.real.Definable L q.codes) {C : J → Set M}
    (hC : Relation (L := L) p B q C) :
    Relation (L := L) p B q (fun j => (C j)ᶜ) := by
  have hd : OverBase (L := L) p B q.codes := OverBase.of_real hq
  change OverBase (L := L) p B (q.relationPullback (fun j => (C j)ᶜ))
  convert OverBase.inter (hd.preimage_comp (Sum.inl : η → η ⊕ Fin 1))
    (OverBase.compl hC hp) hp using 1
  ext z
  exact ⟨fun ⟨hz,hn⟩ => ⟨hz,fun ⟨_,h⟩ => hn h⟩,
    fun ⟨hz,hn⟩ => ⟨hz,fun h => hn ⟨hz,h⟩⟩⟩

omit [Finite η] in
theorem Relation.domain {C : J → Set M} (hC : Relation (L := L) p B q C) :
    Family (L := L) p B q {j | (C j).Nonempty} := by
  change OverBase (L := L) p B (q.pullback {j | (C j).Nonempty})
  convert OverBase.exists_block hC using 1
  ext z
  exact ⟨fun ⟨hz,x,hx⟩ => ⟨![x],hz,hx⟩,
    fun ⟨x,hz,hx⟩ => ⟨hz,x 0,hx⟩⟩

include hp in
theorem Family.inter {T U : Set J}
    (hT : Family (L := L) p B q T) (hU : Family (L := L) p B q U) :
    Family (L := L) p B q (T ∩ U) := by
  change OverBase (L := L) p B (q.pullback (T ∩ U))
  convert OverBase.inter hT hU hp using 1
  ext z
  exact ⟨fun ⟨hz,ht,hu⟩ => ⟨⟨hz,ht⟩,hz,hu⟩,
    fun ⟨⟨hz,ht⟩,_,hu⟩ => ⟨hz,ht,hu⟩⟩

include hp in
theorem Relation.restrict {T : Set J} {C : J → Set M}
    (hT : Family (L := L) p B q T) (hC : Relation (L := L) p B q C) :
    Relation (L := L) p B q (fun j => {x | j ∈ T ∧ x ∈ C j}) := by
  change OverBase (L := L) p B (q.relationPullback (fun j => {x | j ∈ T ∧ x ∈ C j}))
  convert OverBase.inter
    (OverBase.preimage_comp hT (Sum.inl : η → η ⊕ Fin 1)) hC hp using 1
  ext z
  exact ⟨fun ⟨hz,ht,hc⟩ => ⟨⟨hz,ht⟩,hz,hc⟩,
    fun ⟨⟨hz,ht⟩,_,hc⟩ => ⟨hz,ht,hc⟩⟩

theorem Relation.range {C : J → Set M} (hC : Relation (L := L) p B q C) :
    OverBase (L := L) p B {z : Fin 1 → M | ∃ j, z 0 ∈ C j} := by
  have h := (OverBase.preimage_comp hC (Sum.swap : η ⊕ Fin 1 → Fin 1 ⊕ η)).exists_block
  convert h using 1
  ext z
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨c,rfl⟩ := q.onto j
    exact ⟨c.val,c.property,hj⟩
  · rintro ⟨c,hc,hj⟩
    exact ⟨q.decode ⟨c,hc⟩,hj⟩

include hp in
theorem exceptional_definable (hq : B.real.Definable L q.codes)
    {T : Set J} {C P : J → Set M}
    (hT : Family (L := L) p B q T)
    (hC : Relation (L := L) p B q C) (hP : Relation (L := L) p B q P) :
    Family (L := L) p B q (ImaginaryFamilies.exceptional T C P) := by
  have hc := Relation.inter hp hC hP
  have hn := Relation.inter hp hC (Relation.compl hp hq hP)
  have hd := Family.inter hp hT (Family.inter hp hc.domain hn.domain)
  change OverBase (L := L) p B (q.pullback (ImaginaryFamilies.exceptional T C P))
  change OverBase (L := L) p B (q.pullback _) at hd
  convert hd using 1
  ext z
  exact ⟨fun ⟨hz,ht,x,hxc,hxp,y,hyc,hyp⟩ => ⟨hz,ht,⟨x,hxc,hxp⟩,y,hyc,hyp⟩,
    fun ⟨hz,ht,⟨x,hxc,hxp⟩,y,hyc,hyp⟩ => ⟨hz,ht,x,hxc,hxp,y,hyc,hyp⟩⟩

include hp in
theorem traces_definable (hq : B.real.Definable L q.codes)
    {T : Set J} {C P : J → Set M}
    (hT : Family (L := L) p B q T)
    (hC : Relation (L := L) p B q C) (hP : Relation (L := L) p B q P) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ ImaginaryFamilies.traces T C P} :=
  Relation.range (Relation.restrict hp (exceptional_definable hp hq hT hC hP)
    (Relation.inter hp hC hP))

include hp in
theorem Family.image_on {A T : Set J} {f : J → J}
    (hA : Family (L := L) p B q A)
    (hf : OverBase (L := L) p B (q.functionPullback T f)) :
    Family (L := L) p B q (f '' (A ∩ T)) := by
  have hi := OverBase.inter
    (OverBase.preimage_comp hA (Sum.inl : η → η ⊕ η)) hf hp
  have hd := (hi.preimage_comp (Sum.swap : η ⊕ η → η ⊕ η)).exists_block
  change OverBase (L := L) p B (q.pullback (f '' (A ∩ T)))
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,i,⟨hi,hiT⟩,hfi⟩
    obtain ⟨c,rfl⟩ := q.onto i
    exact ⟨c.val,⟨c.property,hi⟩,c.property,hz,hiT,hfi⟩
  · rintro ⟨a,⟨ha,hi⟩,_,hb,hiT,hfi⟩
    exact ⟨hb,q.decode ⟨a,ha⟩,⟨hi,hiT⟩,hfi⟩

include hp in
theorem Algebraic.map_on {T : Set J} {f : J → J} {i : J}
    (hi : Algebraic (L := L) p B q i) (hiT : i ∈ T)
    (hf : OverBase (L := L) p B (q.functionPullback T f)) :
    Algebraic (L := L) p B q (f i) := by
  obtain ⟨A,hA,hfin,hi⟩ := hi
  exact ⟨f '' (A ∩ T),Family.image_on hp hA hf,
    (hfin.inter_of_left T).image f,i,⟨hi,hiT⟩,rfl⟩

include hp in
theorem Relation.comp_on {T : Set J} {f : J → J} {R : J → Set M}
    (hR : Relation (L := L) p B q R)
    (hf : OverBase (L := L) p B (q.functionPullback T f)) :
    Relation (L := L) p B q (fun i => {x | i ∈ T ∧ x ∈ R (f i)}) := by
  let πf : η ⊕ η → (η ⊕ Fin 1) ⊕ η :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πR : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ η :=
    Sum.elim Sum.inr (fun i => .inl (.inr i))
  have hd := (OverBase.inter (hf.preimage_comp πf)
    (OverBase.preimage_comp hR πR) hp).exists_block
  change OverBase (L := L) p B (q.relationPullback (fun i => {x | i ∈ T ∧ x ∈ R (f i)}))
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,ht,hx⟩
    obtain ⟨c,hc⟩ := q.onto (f (q.decode ⟨z ∘ Sum.inl,hz⟩))
    exact ⟨c.val,⟨hz,c.property,ht,hc.symm⟩,c.property,hc.symm ▸ hx⟩
  · rintro ⟨c,⟨hz,hc,ht,hfi⟩,_,hx⟩
    exact ⟨hz,ht,hfi.symm ▸ hx⟩

variable [Finite κ]

include hp in
theorem finite_exceptional (hq : B.real.Definable L q.codes)
    {D : Set M} {balls : Set (Set M)} (hlam : IsLaminar balls)
    (hcm : ∀ Q' : Set M, CMinimalOn L Q' D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    {T : Set J} {C P : J → Set M}
    (hT : Family (L := L) p B q T)
    (hC : Relation (L := L) p B q C) (hP : Relation (L := L) p B q P)
    (hballs : ∀ j ∈ T, C j ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j)) :
    (ImaginaryFamilies.exceptional T C P).Finite := by
  have hsupport := ImaginaryParameters.finite_ball_support hcm
    (traces_definable hp hq hT hC hP) (by
      rintro x ⟨i,hi,hxc,_⟩
      exact hsub _ (hballs i hi.1) hxc)
  have hpair : Pairwise fun i j : T => Disjoint (C i.val) (C j.val) := by
    intro i j hne
    exact hdis i.property j.property (fun he => hne (Subtype.ext he))
  have hf := finite_splitters hlam (fun i : T => C i.val)
    (fun i => hballs i.val i.property) hpair hsupport
  apply (hf.image Subtype.val).subset
  intro i hi
  exact ⟨⟨i,hi.1⟩,ImaginaryFamilies.splits_traces hdis hi,rfl⟩

omit [Finite κ] in
include hp in
theorem atomic_below_complete_type (hq : B.real.Definable L q.codes)
    {T : Set J} {C : J → Set M}
    (hT : Family (L := L) p B q T) (hC : Relation (L := L) p B q C)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {A : Set M} (hA : CompleteType (L := L) p B A)
    {i : J} (hi : i ∈ T) (hisub : C i ⊆ A) :
    AtomicWith (L := L) p B q i (C i) := by
  classical
  refine ⟨⟨C,hC,rfl⟩,?_⟩
  rintro S ⟨P,hP,rfl⟩
  have hcut : ¬ Splits (P i) (C i) := by
    intro hc
    obtain ⟨x,hxc,hxU,y,hyc,hyU⟩ := ImaginaryFamilies.splits_traces hdis ⟨hi,hc⟩
    rcases hA _ (traces_definable hp hq hT hC hP) with hw | hd
    · exact hyU (hw (hisub hyc))
    · exact Set.disjoint_left.mp hd (hisub hxc) hxU
  by_cases hwhole : C i ⊆ P i
  · exact Or.inl hwhole
  · obtain ⟨y,hy,hyp⟩ := Set.not_subset.mp hwhole
    exact Or.inr (Set.disjoint_left.mpr fun x hx hxp => hcut ⟨x,hx,hxp,y,hy,hyp⟩)

include hp in
theorem parametric_atomic (hq : B.real.Definable L q.codes)
    {D : Set M} {balls : Set (Set M)} (hlam : IsLaminar balls)
    (hcm : ∀ Q' : Set M, CMinimalOn L Q' D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    {T : Set J} {C : J → Set M}
    (hT : Family (L := L) p B q T) (hC : Relation (L := L) p B q C)
    (hballs : ∀ i ∈ T, C i ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {i : J} (hi : i ∈ T) (hna : ¬ Algebraic (L := L) p B q i) :
    AtomicWith (L := L) p B q i (C i) := by
  classical
  refine ⟨⟨C,hC,rfl⟩,?_⟩
  rintro S ⟨P,hP,rfl⟩
  have hcut : ¬ Splits (P i) (C i) := by
    intro hc
    exact hna ⟨ImaginaryFamilies.exceptional T C P,exceptional_definable hp hq hT hC hP,
      finite_exceptional hp hq hlam hcm hsub hT hC hP hballs hdis,hi,hc⟩
  by_cases hwhole : C i ⊆ P i
  · exact Or.inl hwhole
  · obtain ⟨y,hy,hyp⟩ := Set.not_subset.mp hwhole
    exact Or.inr (Set.disjoint_left.mpr fun x hx hxp => hcut ⟨x,hx,hxp,y,hy,hyp⟩)

include hp in
theorem parametric_atomic_of_output (hq : B.real.Definable L q.codes)
    {D : Set M} {balls : Set (Set M)} (hlam : IsLaminar balls)
    (hcm : ∀ Q' : Set M, CMinimalOn L Q' D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    {T : Set J} {C : J → Set M}
    (hT : Family (L := L) p B q T) (hC : Relation (L := L) p B q C)
    (hballs : ∀ i ∈ T, C i ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {f : J → J} (hf : OverBase (L := L) p B (q.functionPullback T f))
    {i : J} (hi : i ∈ T) (hna : ¬ Algebraic (L := L) p B q (f i)) :
    AtomicWith (L := L) p B q i (C i) :=
  parametric_atomic hp hq hlam hcm hsub hT hC hballs hdis hi
    (fun ha => hna (Algebraic.map_on hp ha hi hf))

omit [Finite κ] in
/-- Existential projection of an interpreted binary relation, quantifying
all codes of the first component over the same original base. -/
theorem pair_domain {R : Set (Fin 2 → J)}
    (hR : OverBase (L := L) p B ((tuplePresentation q (Fin 2)).pullback R)) :
    Family (L := L) p B q {j | ∃ k, ![k,j] ∈ R} := by
  let π : Fin 2 × η → η ⊕ η :=
    fun (i,a) => Fin.cases (.inr a) (fun _ => .inl a) i
  have hex := OverBase.exists_block (hR.preimage_comp π)
  change OverBase (L := L) p B (q.pullback {j | ∃ k, ![k,j] ∈ R})
  convert hex using 1
  ext c
  change (∃ hc : c ∈ q.codes, ∃ k, ![k,q.decode ⟨c,hc⟩] ∈ R) ↔
    ∃ d : η → M, ∃ hd : Sum.elim c d ∘ π ∈ tupleCodes q (Fin 2),
      (tuplePresentation q (Fin 2)).decode ⟨Sum.elim c d ∘ π,hd⟩ ∈ R
  have he (d : η → M) (hc : c ∈ q.codes) (hd : d ∈ q.codes)
      (hcd : Sum.elim c d ∘ π ∈ tupleCodes q (Fin 2)) :
      (tuplePresentation q (Fin 2)).decode ⟨Sum.elim c d ∘ π,hcd⟩ =
        ![q.decode ⟨d,hd⟩,q.decode ⟨c,hc⟩] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨hc,k,hk⟩
    obtain ⟨d,hd⟩ := q.onto k
    have hcd : Sum.elim c d.val ∘ π ∈ tupleCodes q (Fin 2) := by
      intro i
      fin_cases i
      · exact d.property
      · exact hc
    refine ⟨d.val,hcd,?_⟩
    rw [he d.val hc d.property hcd,hd]
    exact hk
  · rintro ⟨d,hcd,hr⟩
    have hc : c ∈ q.codes := hcd 1
    have hd : d ∈ q.codes := hcd 0
    rw [he d hc hd hcd] at hr
    exact ⟨hc,q.decode ⟨d,hd⟩,hr⟩


end IntegrationInACVF.Section3.ImaginaryBaseFamilies
