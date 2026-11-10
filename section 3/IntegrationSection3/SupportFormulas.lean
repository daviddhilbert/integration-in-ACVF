module

public import IntegrationSection3.MinimalBallSupport
public import IntegrationSection3.ImaginaryBaseFamilies

@[expose] public section

/-! Intrinsic finite-support formulas with all interpreted codes retained.
Tuple support and membership in a fixed-length support family are definable
over the original base. Minimal-support uniqueness identifies that family
with the canonical finite support, without naming a chosen enumeration. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.SupportFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

theorem imp_definable {α : Type*} [Finite α] (hp : B.real.Definable L p.codes)
    {P Q : Set (α → M)} (hP : OverBase (L := L) p B P) (hQ : OverBase (L := L) p B Q) :
    OverBase (L := L) p B {z | z ∈ P → z ∈ Q} := by
  convert OverBase.compl (OverBase.inter hP (OverBase.compl hQ hp) hp) hp using 1
  ext z
  change (_ → _) ↔ ¬ (_ ∧ ¬ _)
  tauto

theorem iff_definable {α : Type*} [Finite α] (hp : B.real.Definable L p.codes)
    {P Q : Set (α → M)} (hP : OverBase (L := L) p B P) (hQ : OverBase (L := L) p B Q) :
    OverBase (L := L) p B {z | z ∈ P ↔ z ∈ Q} := by
  convert OverBase.inter (imp_definable hp hP hQ) (imp_definable hp hQ hP) hp using 1
  ext z
  exact iff_iff_implies_and_implies

def row {n : ℕ} (c : Fin n × η → M) (i : Fin n) (x : M) : η ⊕ Fin 1 → M :=
  Sum.elim (fun j => c (i,j)) ![x]

def SupportCodes (q : Presentation M J η) (U : J → Set M) (A : Set M) (n : ℕ) :
    Set (Fin n × η → M) :=
  {c | c ∈ tupleCodes q (Fin n) ∧ ∀ t : Fin 2 → M,
    (∀ i, row c i (t 0) ∈ q.relationPullback U ↔ row c i (t 1) ∈ q.relationPullback U) →
      (t 0 ∈ A ↔ t 1 ∈ A)}

theorem supportCodes_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {A : Set M} (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A}) (n : ℕ) :
    OverBase (L := L) p B (SupportCodes q U A n) := by
  let π (i : Fin n) (j : Fin 2) : η ⊕ Fin 1 → (Fin n × η) ⊕ Fin 2 :=
    Sum.elim (fun a => .inl (i,a)) (fun _ => .inr j)
  have hm (i : Fin n) (j : Fin 2) := OverBase.preimage_comp hU (π i j)
  have ha (j : Fin 2) := hA.preimage_comp (fun _ : Fin 1 => (Sum.inr j : (Fin n × η) ⊕ Fin 2))
  have hrows := OverBase.forall_finite
    (fun i : Fin n => iff_definable hp (hm i 0) (hm i 1)) hp
  have hpoints := iff_definable hp (ha 0) (ha 1)
  have hall := OverBase.forall_block (imp_definable hp hrows hpoints) hp
  have hcodes := OverBase.of_real (p := p) (B := B) (tupleCodes_definable hq (Fin n))
  convert OverBase.inter hcodes hall hp using 1
  ext c
  have he (t : Fin 2 → M) (i : Fin n) (j : Fin 2) : Sum.elim c t ∘ π i j = row c i (t j) := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => fin_cases a; rfl
  change (c ∈ tupleCodes q (Fin n) ∧ ∀ t : Fin 2 → M,
      (∀ i, row c i (t 0) ∈ q.relationPullback U ↔ row c i (t 1) ∈ q.relationPullback U) →
        (t 0 ∈ A ↔ t 1 ∈ A)) ↔
    (c ∈ tupleCodes q (Fin n) ∧ ∀ t : Fin 2 → M,
      (∀ i, Sum.elim c t ∘ π i 0 ∈ q.relationPullback U ↔
        Sum.elim c t ∘ π i 1 ∈ q.relationPullback U) → (t 0 ∈ A ↔ t 1 ∈ A))
  simp only [he]

omit [Finite η] in
theorem mem_supportCodes_iff {U : J → Set M} {A : Set M} {n : ℕ}
    (c : Fin n × η → M) (hc : c ∈ tupleCodes q (Fin n)) :
    c ∈ SupportCodes q U A n ↔
      MinimalBallSupport.Supports
        (Finset.univ.image (fun i : Fin n => U (q.decode ⟨(fun j => c (i,j)),hc i⟩))) A := by
  classical
  let f : Fin n → Set M := fun i => U (q.decode ⟨(fun j => c (i,j)),hc i⟩)
  have hm (i : Fin n) (x : M) : row c i x ∈ q.relationPullback U ↔ x ∈ f i :=
    q.mem_relationPullback U ⟨(fun j => c (i,j)),hc i⟩ x
  constructor
  · rintro ⟨_,h⟩ x y hxy
    apply h ![x,y]
    intro i
    exact (hm i x).trans ((hxy (f i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)).trans
      (hm i y).symm)
  · intro h
    refine ⟨hc,fun t ht => h (t 0) (t 1) ?_⟩
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact (hm i (t 0)).symm.trans ((ht i).trans (hm i (t 1)))


theorem exists_finite {α τ : Type*} [Finite α] [Finite τ]
    (hp : B.real.Definable L p.codes) {P : τ → Set (α → M)}
    (hP : ∀ t, OverBase (L := L) p B (P t)) :
    OverBase (L := L) p B {z | ∃ t, z ∈ P t} := by
  convert OverBase.compl (OverBase.forall_finite (fun t => OverBase.compl (hP t) hp) hp) hp using 1
  ext z
  change (∃ t, z ∈ P t) ↔ ¬ ∀ t, ¬ z ∈ P t
  exact not_forall_not.symm

def SupportFamily (U : J → Set M) (A : Set M) (n : ℕ) : Set J :=
  {j | ∃ t : Fin n → J,
    MinimalBallSupport.Supports (Finset.univ.image (fun i => U (t i))) A ∧ j ∈ Set.range t}

theorem supportFamily_definable (hp : B.real.Definable L p.codes)
    (hq : q.IsDefinable L B.real) {U : J → Set M}
    (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {A : Set M} (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A}) (n : ℕ) :
    ImaginaryBaseFamilies.Family (L := L) p B q (SupportFamily U A n) := by
  let π (i : Fin n) : η ⊕ η → η ⊕ (Fin n × η) :=
    Sum.elim (fun a => .inr (i,a)) Sum.inl
  have hc := (supportCodes_definable hp hq.1 hU hA n).preimage_comp
    (Sum.inr : Fin n × η → η ⊕ (Fin n × η))
  have hqe := OverBase.of_real (p := p) (B := B) hq.2
  have heq := exists_finite hp (fun i : Fin n => hqe.preimage_comp (π i))
  have hex := OverBase.exists_block (OverBase.inter hc heq hp)
  have hguard := OverBase.of_real (p := p) (B := B) hq.1
  change OverBase (L := L) p B (q.pullback (SupportFamily U A n))
  convert OverBase.inter hguard hex hp using 1
  ext g
  have hcomp (c : Fin n × η → M) (i : Fin n) :
      Sum.elim g c ∘ π i = Sum.elim (fun a => c (i,a)) g := by
    funext a
    cases a <;> rfl
  change (∃ hg : g ∈ q.codes, ∃ t : Fin n → J,
      MinimalBallSupport.Supports (Finset.univ.image (fun i => U (t i))) A ∧
        ∃ i, t i = q.decode ⟨g,hg⟩) ↔
    (g ∈ q.codes ∧ ∃ c : Fin n × η → M, c ∈ SupportCodes q U A n ∧
      ∃ i : Fin n,
        (Sum.elim g c ∘ π i) ∈
          {z : η ⊕ η → M | ∃ h : z ∘ Sum.inl ∈ q.codes,
            ∃ h' : z ∘ Sum.inr ∈ q.codes,
              q.decode ⟨z ∘ Sum.inl,h⟩ = q.decode ⟨z ∘ Sum.inr,h'⟩})
  simp only [hcomp]
  constructor
  · rintro ⟨hg,t,ht,i,hi⟩
    obtain ⟨c,hct⟩ := (tuplePresentation q (Fin n)).onto t
    have hcs : c.val ∈ SupportCodes q U A n := by
      apply (mem_supportCodes_iff c.val c.property).mpr
      change MinimalBallSupport.Supports
        (Finset.univ.image (fun i => U ((tuplePresentation q (Fin n)).decode c i))) A
      rw [hct]
      exact ht
    refine ⟨hg,c.val,hcs,i,c.property i,hg,?_⟩
    exact (congrFun hct i).trans hi
  · rintro ⟨hg,c,hcs,i,hci,hg',he⟩
    let ct : (tuplePresentation q (Fin n)).codes := ⟨c,hcs.1⟩
    let t := (tuplePresentation q (Fin n)).decode ct
    refine ⟨hg,t,(mem_supportCodes_iff c hcs.1).mp hcs,i,?_⟩
    exact he


omit [Finite η] in
theorem supportFamily_eq_preimage {U : J → Set M} (hUinj : Function.Injective U)
    {balls : Set (Set M)} (hl : IsLaminar balls) (htop : (Set.univ : Set M) ∈ balls)
    (hav : MinimalBallSupport.AvoidsFiniteProperSubballs balls)
    {F : Finset (Set M)} {A : Set M} (hF : MinimalBallSupport.IsMinimalSupport balls F A)
    (hU : ∀ j, U j ∈ balls) (hcover : ∀ b ∈ F, ∃ j, U j = b) :
    SupportFamily U A F.card = U ⁻¹' (F : Set (Set M)) := by
  classical
  ext j
  constructor
  · rintro ⟨t,ht,i,rfl⟩
    let G := Finset.univ.image (fun i => U (t i))
    have hG : MinimalBallSupport.IsSupport balls G A := by
      refine ⟨?_,ht⟩
      intro b hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      exact hU (t i)
    have hFG := MinimalBallSupport.minimal_subset_support hl htop hav hF hG
    have hcard : G.card ≤ F.card := by
      calc
        G.card ≤ (Finset.univ : Finset (Fin F.card)).card := Finset.card_image_le
        _ = F.card := by simp
    have he : F = G := Finset.eq_of_subset_of_card_le hFG hcard
    have hti : U (t i) ∈ G := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
    exact he.symm ▸ hti
  · intro hj
    let e : Fin F.card ≃ F := F.equivFin.symm
    choose t ht using fun i : Fin F.card => hcover (e i).val (e i).property
    have himage : Finset.univ.image (fun i => U (t i)) = F := by
      ext b
      constructor
      · intro hb
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
        exact (ht i).symm ▸ (e i).property
      · intro hb
        let i := e.symm ⟨b,hb⟩
        have he : (e i).val = b := congrArg Subtype.val (e.apply_symm_apply ⟨b,hb⟩)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,(ht i).trans he⟩
    have hsup : MinimalBallSupport.Supports (Finset.univ.image (fun i => U (t i))) A := by
      rw [himage]
      exact hF.1.2
    let i := e.symm ⟨U j,hj⟩
    have he : (e i).val = U j := congrArg Subtype.val (e.apply_symm_apply ⟨U j,hj⟩)
    exact ⟨t,hsup,i,hUinj ((ht i).trans he)⟩

end IntegrationInACVF.Section3.SupportFormulas
