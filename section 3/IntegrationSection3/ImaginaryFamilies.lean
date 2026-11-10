module

public import IntegrationSection3.ParametricAtomicity

@[expose] public section

/-!
# Families on an interpreted quotient sort

Definability is tested on the full preimage of every imaginary element, as
in the predecessor's `GammaParameters` and ball-quotient interfaces. A real
representative is never adjoined to the parameter base. The finite-exception
argument can consequently be applied to imaginary indices directly.

`Presentation` is only coding data. `IsDefinable` additionally requires the
code domain and the equality relation of the quotient to be first-order
definable. No C-minimality, algebraicity or atomicity conclusion is included.
-/

open Set FirstOrder

namespace IntegrationInACVF.Section3.ImaginaryFamilies

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''

structure Presentation (M : Type w) (I : Type w') (κ : Type w'') where
  codes : Set (κ → M)
  decode : codes → I
  onto : Function.Surjective decode

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} [Finite κ]

namespace Presentation

variable (p : Presentation M I κ)

/-- Full preimage, including every representative of each element. -/
def pullback (A : Set I) : Set (κ → M) :=
  {z | ∃ hz : z ∈ p.codes, p.decode ⟨z,hz⟩ ∈ A}

def relationPullback (R : I → Set M) : Set (κ ⊕ Fin 1 → M) :=
  {z | ∃ hz : z ∘ Sum.inl ∈ p.codes,
    z (.inr 0) ∈ R (p.decode ⟨z ∘ Sum.inl,hz⟩)}

/-- The usual definable interpretation of equality on this quotient sort. -/
def IsDefinable (L : Language.{u,v}) [L.Structure M] (Q : Set M) : Prop :=
  Q.Definable L p.codes ∧ Q.Definable L
    {z : κ ⊕ κ → M | ∃ h : z ∘ Sum.inl ∈ p.codes,
      ∃ h' : z ∘ Sum.inr ∈ p.codes,
      p.decode ⟨z ∘ Sum.inl,h⟩ = p.decode ⟨z ∘ Sum.inr,h'⟩}

def DefinableFamily (Q : Set M) (A : Set I) : Prop := Q.Definable L (p.pullback A)

def DefinableRelation (Q : Set M) (R : I → Set M) : Prop :=
  Q.Definable L (p.relationPullback R)

/-- A finite imaginary parameter is interpreted through a full invariant
relation over the original real base, rather than through a chosen code. -/
def DefinableWith (Q : Set M) (i : I) (A : Set M) : Prop :=
  ∃ R : I → Set M, p.DefinableRelation (L := L) Q R ∧ R i = A

def Algebraic (Q : Set M) (i : I) : Prop :=
  ∃ A : Set I, p.DefinableFamily (L := L) Q A ∧ A.Finite ∧ i ∈ A

def AtomicWith (Q : Set M) (i : I) (A : Set M) : Prop :=
  p.DefinableWith (L := L) Q i A ∧
    ∀ S : Set M, p.DefinableWith (L := L) Q i S → A ⊆ S ∨ Disjoint A S

/-- Full graph of a function defined on an imaginary domain. -/
def functionPullback (T : Set I) (f : I → I) : Set (κ ⊕ κ → M) :=
  {z | ∃ h : z ∘ Sum.inl ∈ p.codes, ∃ h' : z ∘ Sum.inr ∈ p.codes,
    p.decode ⟨z ∘ Sum.inl,h⟩ ∈ T ∧
      f (p.decode ⟨z ∘ Sum.inl,h⟩) = p.decode ⟨z ∘ Sum.inr,h'⟩}

omit [Finite κ] in
theorem mem_pullback (A : Set I) (q : p.codes) :
    q.val ∈ p.pullback A ↔ p.decode q ∈ A := by
  constructor
  · rintro ⟨h,hA⟩; exact hA
  · exact fun hA => ⟨q.property,hA⟩

omit [Finite κ] in
theorem mem_relationPullback (R : I → Set M) (q : p.codes) (x : M) :
    Sum.elim q.val ![x] ∈ p.relationPullback R ↔ x ∈ R (p.decode q) := by
  constructor
  · rintro ⟨h,hR⟩; exact hR
  · exact fun hR => ⟨q.property,hR⟩

variable {p} {Q : Set M}

omit [Finite κ] in
/-- Equality of interpreted objects is first-order definable when they have
an injective, definable membership representation. This applies to actual
ball imaginaries, whose equality is equality of their underlying point sets. -/
theorem isDefinable_of_membership (p : Presentation M I κ) (U : I → Set M)
    (hinj : Function.Injective U) (hcodes : Q.Definable L p.codes)
    (hU : p.DefinableRelation (L := L) Q U) : p.IsDefinable L Q := by
  let πl : κ ⊕ Fin 1 → (κ ⊕ κ) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πr : κ ⊕ Fin 1 → (κ ⊕ κ) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inr i)) Sum.inr
  have hl := hU.preimage_comp πl
  have hr := hU.preimage_comp πr
  have he : Q.Definable L {z : (κ ⊕ κ) ⊕ Fin 1 → M |
      z ∘ πl ∈ p.relationPullback U ↔ z ∘ πr ∈ p.relationPullback U} := by
    convert (hl.himp hr).inter (hr.himp hl) using 1
    ext z
    change (_ ↔ _) ↔ ((_ → _) ∧ (_ → _))
    exact iff_iff_implies_and_implies
  have hall := he.forall_of_finite
  refine ⟨hcodes,?_⟩
  convert (hcodes.preimage_comp (Sum.inl : κ → κ ⊕ κ)).inter
    ((hcodes.preimage_comp (Sum.inr : κ → κ ⊕ κ)).inter hall) using 1
  ext z
  constructor
  · rintro ⟨hz,hz',heq⟩
    refine ⟨hz,hz',?_⟩
    intro u
    change (∃ h : z ∘ Sum.inl ∈ p.codes,
      u 0 ∈ U (p.decode ⟨z ∘ Sum.inl,h⟩)) ↔
      (∃ h : z ∘ Sum.inr ∈ p.codes,
        u 0 ∈ U (p.decode ⟨z ∘ Sum.inr,h⟩))
    constructor
    · rintro ⟨_,hu⟩; exact ⟨hz',heq ▸ hu⟩
    · rintro ⟨_,hu⟩; exact ⟨hz,heq.symm ▸ hu⟩
  · rintro ⟨hz,hz',heq⟩
    refine ⟨hz,hz',hinj (Set.ext fun x => ?_)⟩
    have hx := heq ![x]
    change (∃ h : z ∘ Sum.inl ∈ p.codes,
      x ∈ U (p.decode ⟨z ∘ Sum.inl,h⟩)) ↔
      (∃ h : z ∘ Sum.inr ∈ p.codes,
        x ∈ U (p.decode ⟨z ∘ Sum.inr,h⟩)) at hx
    exact ⟨fun h => (hx.mp ⟨hz,h⟩).choose_spec,
      fun h => (hx.mpr ⟨hz',h⟩).choose_spec⟩

omit [Finite κ] in
theorem DefinableRelation.inter {R S : I → Set M}
    (hR : p.DefinableRelation (L := L) Q R)
    (hS : p.DefinableRelation (L := L) Q S) :
    p.DefinableRelation (L := L) Q (fun i => R i ∩ S i) := by
  change Q.Definable L (p.relationPullback (fun i => R i ∩ S i))
  convert Set.Definable.inter hR hS using 1
  ext z
  constructor
  · rintro ⟨hz,hR,hS⟩
    exact ⟨⟨hz,hR⟩,hz,hS⟩
  · rintro ⟨⟨hz,hR⟩,⟨_,hS⟩⟩
    exact ⟨hz,hR,hS⟩

omit [Finite κ] in
theorem DefinableRelation.compl (hp : p.IsDefinable L Q) {R : I → Set M}
    (hR : p.DefinableRelation (L := L) Q R) :
    p.DefinableRelation (L := L) Q (fun i => (R i)ᶜ) := by
  change Q.Definable L (p.relationPullback (fun i => (R i)ᶜ))
  convert (hp.1.preimage_comp (Sum.inl : κ → κ ⊕ Fin 1)).inter
    (Set.Definable.compl hR) using 1
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    refine ⟨hz,?_⟩
    rintro ⟨_,h⟩
    exact hn h
  · rintro ⟨hz,hn⟩
    exact ⟨hz,fun h => hn ⟨hz,h⟩⟩

/-- Existential quantification in the real coordinate preserves the base. -/
theorem DefinableRelation.domain {R : I → Set M}
    (hR : p.DefinableRelation (L := L) Q R) :
    p.DefinableFamily (L := L) Q {i | (R i).Nonempty} := by
  change Q.Definable L (p.pullback {i | (R i).Nonempty})
  convert hR.image_comp (Sum.inl : κ → κ ⊕ Fin 1) using 1
  ext z
  constructor
  · rintro ⟨hz,x,hx⟩
    exact ⟨Sum.elim z ![x],⟨hz,hx⟩,rfl⟩
  · rintro ⟨a,⟨hz,hx⟩,rfl⟩
    exact ⟨hz,a (.inr 0),hx⟩

omit [Finite κ] in
theorem DefinableFamily.inter {A B : Set I}
    (hA : p.DefinableFamily (L := L) Q A)
    (hB : p.DefinableFamily (L := L) Q B) :
    p.DefinableFamily (L := L) Q (A ∩ B) := by
  change Q.Definable L (p.pullback (A ∩ B))
  convert Set.Definable.inter hA hB using 1
  ext z
  constructor
  · rintro ⟨hz,ha,hb⟩
    exact ⟨⟨hz,ha⟩,hz,hb⟩
  · rintro ⟨⟨hz,ha⟩,⟨_,hb⟩⟩
    exact ⟨hz,ha,hb⟩

omit [Finite κ] in
theorem DefinableRelation.restrict {A : Set I} {R : I → Set M}
    (hA : p.DefinableFamily (L := L) Q A)
    (hR : p.DefinableRelation (L := L) Q R) :
    p.DefinableRelation (L := L) Q (fun i => {x | i ∈ A ∧ x ∈ R i}) := by
  change Q.Definable L (p.relationPullback (fun i => {x | i ∈ A ∧ x ∈ R i}))
  convert (hA.preimage_comp (Sum.inl : κ → κ ⊕ Fin 1)).inter hR using 1
  ext z
  constructor
  · rintro ⟨hz,ha,hr⟩
    exact ⟨⟨hz,ha⟩,hz,hr⟩
  · rintro ⟨⟨hz,ha⟩,⟨_,hr⟩⟩
    exact ⟨hz,ha,hr⟩

/-- Quantifying over imaginary indices uses all real codes and surjectivity.
No parameter naming a representative enters the resulting unary set. -/
theorem DefinableRelation.range {R : I → Set M}
    (hR : p.DefinableRelation (L := L) Q R) :
    Q.Definable₁ L {x | ∃ i, x ∈ R i} := by
  have hd := hR.image_comp (Sum.inr : Fin 1 → κ ⊕ Fin 1)
  change Q.Definable L {z : Fin 1 → M | ∃ i, z 0 ∈ R i}
  convert hd using 1
  ext z
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨q,rfl⟩ := p.onto i
    exact ⟨Sum.elim q.val z,⟨q.property,hi⟩,rfl⟩
  · rintro ⟨a,⟨ha,hr⟩,haz⟩
    exact ⟨p.decode ⟨a ∘ Sum.inl,ha⟩,by
      simpa only [← congrFun haz 0,Function.comp_apply] using hr⟩

theorem DefinableFamily.image_on {A T : Set I} {f : I → I}
    (hA : p.DefinableFamily (L := L) Q A)
    (hf : Q.Definable L (p.functionPullback T f)) :
    p.DefinableFamily (L := L) Q (f '' (A ∩ T)) := by
  have hd := ((hA.preimage_comp (Sum.inl : κ → κ ⊕ κ)).inter hf).image_comp
    (Sum.inr : κ → κ ⊕ κ)
  change Q.Definable L (p.pullback (f '' (A ∩ T)))
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,i,⟨hi,hiT⟩,hfi⟩
    obtain ⟨q,rfl⟩ := p.onto i
    exact ⟨Sum.elim q.val z,⟨⟨q.property,hi⟩,q.property,hz,hiT,hfi⟩,rfl⟩
  · rintro ⟨a,⟨⟨ha,hi⟩,_,hb,hiT,hfi⟩,rfl⟩
    exact ⟨hb,p.decode ⟨a ∘ Sum.inl,ha⟩,⟨hi,hiT⟩,hfi⟩

/-- Algebraicity transfers through a same-base definable partial function
of imaginaries. Neither its input nor its output code is named. -/
theorem Algebraic.map_on {T : Set I} {f : I → I} {i : I}
    (hi : p.Algebraic (L := L) Q i) (hiT : i ∈ T)
    (hf : Q.Definable L (p.functionPullback T f)) :
    p.Algebraic (L := L) Q (f i) := by
  obtain ⟨A,hA,hfin,hi⟩ := hi
  exact ⟨f '' (A ∩ T),hA.image_on hf,(hfin.inter_of_left T).image f,i,⟨hi,hiT⟩,rfl⟩

/-- Compose a definable imaginary function with a full invariant relation.
Existentially quantifying the output code eliminates it from the base. -/
theorem DefinableRelation.comp_on {T : Set I} {f : I → I} {R : I → Set M}
    (hR : p.DefinableRelation (L := L) Q R)
    (hf : Q.Definable L (p.functionPullback T f)) :
    p.DefinableRelation (L := L) Q (fun i => {x | i ∈ T ∧ x ∈ R (f i)}) := by
  let πf : κ ⊕ κ → (κ ⊕ Fin 1) ⊕ κ :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πR : κ ⊕ Fin 1 → (κ ⊕ Fin 1) ⊕ κ :=
    Sum.elim Sum.inr (fun i => .inl (.inr i))
  have hd := ((hf.preimage_comp πf).inter (hR.preimage_comp πR)).exists_of_finite
  change Q.Definable L (p.relationPullback (fun i => {x | i ∈ T ∧ x ∈ R (f i)}))
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,ht,hx⟩
    obtain ⟨q,hq⟩ := p.onto (f (p.decode ⟨z ∘ Sum.inl,hz⟩))
    refine ⟨q.val,⟨hz,q.property,ht,hq.symm⟩,q.property,?_⟩
    exact hq.symm ▸ hx
  · rintro ⟨q,⟨hz,hq,ht,hfi⟩,_,hx⟩
    exact ⟨hz,ht,hfi.symm ▸ hx⟩

end Presentation

open Presentation

def exceptional (T : Set I) (C P : I → Set M) : Set I :=
  {i | i ∈ T ∧ Splits (P i) (C i)}

def traces (T : Set I) (C P : I → Set M) : Set M :=
  {x | ∃ i ∈ exceptional T C P, x ∈ C i ∧ x ∈ P i}

variable {p : Presentation M I κ} {Q : Set M} {T : Set I} {C P : I → Set M}

theorem exceptional_definable (hp : p.IsDefinable L Q)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hP : p.DefinableRelation (L := L) Q P) :
    p.DefinableFamily (L := L) Q (exceptional T C P) := by
  have hd := hT.inter ((hC.inter hP).domain.inter (hC.inter (hP.compl hp)).domain)
  change Q.Definable L (p.pullback (exceptional T C P))
  change Q.Definable L (p.pullback _) at hd
  convert hd using 1
  ext z
  constructor
  · rintro ⟨hz,ht,x,hxc,hxp,y,hyc,hyp⟩
    exact ⟨hz,ht,⟨x,hxc,hxp⟩,y,hyc,hyp⟩
  · rintro ⟨hz,ht,⟨x,hxc,hxp⟩,y,hyc,hyp⟩
    exact ⟨hz,ht,x,hxc,hxp,y,hyc,hyp⟩

theorem traces_definable (hp : p.IsDefinable L Q)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hP : p.DefinableRelation (L := L) Q P) : Q.Definable₁ L (traces T C P) :=
  ((hC.inter hP).restrict (exceptional_definable hp hT hC hP)).range

theorem splits_traces (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {i : I} (hi : i ∈ exceptional T C P) : Splits (traces T C P) (C i) := by
  classical
  obtain ⟨hit,x,hxc,hxp,y,hyc,hyp⟩ := hi
  refine ⟨x,hxc,⟨i,⟨hit,x,hxc,hxp,y,hyc,hyp⟩,hxc,hxp⟩,y,hyc,?_⟩
  rintro ⟨j,hj,hyj,hypj⟩
  by_cases he : j = i
  · subst j; exact hyp hypj
  · exact Set.disjoint_left.mp (hdis hj.1 hit he) hyj hyc

theorem finite_exceptional {D : Set M} {balls : Set (Set M)}
    (hp : p.IsDefinable L Q) (hlam : IsLaminar balls)
    (hcm : CMinimalOn L Q D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hP : p.DefinableRelation (L := L) Q P)
    (hballs : ∀ i ∈ T, C i ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j)) :
    (exceptional T C P).Finite := by
  have hsupport := hcm (traces T C P) (traces_definable hp hT hC hP) (by
    rintro x ⟨i,hi,hxc,_⟩
    exact hsub _ (hballs i hi.1) hxc)
  have hpair : Pairwise fun i j : T => Disjoint (C i.val) (C j.val) := by
    intro i j hne
    exact hdis i.property j.property (fun he => hne (Subtype.ext he))
  have hf := finite_splitters hlam (fun i : T => C i.val)
    (fun i => hballs i.val i.property) hpair hsupport
  apply (hf.image Subtype.val).subset
  intro i hi
  exact ⟨⟨i,hi.1⟩,splits_traces hdis hi,rfl⟩

/-- The logical argument behind Lemma 3.4. A definable disjoint family
cannot cut any member contained in a complete-type-generating set: the union
of the proper traces would cut that complete type over the original base.
Here C-minimality and nonalgebraicity are unnecessary. For balls one still
has to supply the actual same-radius family and its definability. -/
theorem atomic_below_complete_type (hp : p.IsDefinable L Q)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {A : Set M} (hA : GeneratesCompleteType L Q {z : Fin 1 → M | z 0 ∈ A})
    {i : I} (hi : i ∈ T) (hisub : C i ⊆ A) :
    p.AtomicWith (L := L) Q i (C i) := by
  classical
  refine ⟨⟨C,hC,rfl⟩,?_⟩
  rintro S ⟨P,hP,rfl⟩
  have hcut : ¬ Splits (P i) (C i) := by
    intro hc
    obtain ⟨x,hxc,hxU,y,hyc,hyU⟩ := splits_traces hdis ⟨hi,hc⟩
    rcases hA {z | z 0 ∈ traces T C P} (traces_definable hp hT hC hP) with hw | hd
    · exact hyU (hw (show ![y] ∈ {z : Fin 1 → M | z 0 ∈ A} from hisub hyc))
    · exact Set.disjoint_left.mp hd
        (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ A} from hisub hxc) hxU
  by_cases hwhole : C i ⊆ P i
  · exact Or.inl hwhole
  · obtain ⟨y,hy,hyp⟩ := Set.not_subset.mp hwhole
    exact Or.inr (Set.disjoint_left.mpr fun x hx hxp => hcut ⟨x,hx,hxp,y,hy,hyp⟩)

/-- Parametric atomicity on an actually interpreted quotient sort. The
nonalgebraicity condition concerns the imaginary, not any real code for it. -/
theorem parametric_atomic {D : Set M} {balls : Set (Set M)}
    (hp : p.IsDefinable L Q) (hlam : IsLaminar balls)
    (hcm : CMinimalOn L Q D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hballs : ∀ i ∈ T, C i ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {i : I} (hi : i ∈ T) (hna : ¬ p.Algebraic (L := L) Q i) :
    p.AtomicWith (L := L) Q i (C i) := by
  classical
  refine ⟨⟨C,hC,rfl⟩,?_⟩
  rintro S ⟨P,hP,rfl⟩
  have hcut : ¬ Splits (P i) (C i) := by
    intro hc
    exact hna ⟨exceptional T C P,exceptional_definable hp hT hC hP,
      finite_exceptional hp hlam hcm hsub hT hC hP hballs hdis,hi,hc⟩
  by_cases hwhole : C i ⊆ P i
  · exact Or.inl hwhole
  · right
    obtain ⟨y,hy,hyp⟩ := Set.not_subset.mp hwhole
    exact Set.disjoint_left.mpr fun x hx hxp => hcut ⟨x,hx,hxp,y,hy,hyp⟩

/-- The nonalgebraicity premise can concern the output-ball imaginary, as
in Lemma 3.2, provided its full same-base function graph is definable. -/
theorem parametric_atomic_of_output {D : Set M} {balls : Set (Set M)}
    (hp : p.IsDefinable L Q) (hlam : IsLaminar balls)
    (hcm : CMinimalOn L Q D balls) (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : p.DefinableFamily (L := L) Q T)
    (hC : p.DefinableRelation (L := L) Q C)
    (hballs : ∀ i ∈ T, C i ∈ balls)
    (hdis : T.Pairwise fun i j => Disjoint (C i) (C j))
    {f : I → I} (hf : Q.Definable L (p.functionPullback T f))
    {i : I} (hi : i ∈ T) (hna : ¬ p.Algebraic (L := L) Q (f i)) :
    p.AtomicWith (L := L) Q i (C i) :=
  parametric_atomic hp hlam hcm hsub hT hC hballs hdis hi
    (fun ha => hna (ha.map_on hi hf))

end IntegrationInACVF.Section3.ImaginaryFamilies
