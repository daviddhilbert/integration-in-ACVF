module

public import IntegrationSection3.ImaginaryTupleAtomicity

@[expose] public section

/-! Definable profiles and atomicity on classes. The finite-exception and
infinite-class hypotheses are geometric inputs, independent of atomicity. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ProfileAtomicity

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {p : Presentation M I κ} {B : Base M I}
variable {m : ℕ}

def graph (f : M → Set (Fin m → M)) : Set (Fin 1 ⊕ Fin m → M) :=
  {z | z ∘ Sum.inr ∈ f (z (.inl 0))}

def sameProfile (f : M → Set (Fin m → M)) : Set (Fin 2 → M) :=
  {z | f (z 0) = f (z 1)}

def badPoints (E : Set (Fin 2 → M)) (f : M → Set (Fin m → M)) : Set M :=
  {x | ∃ y z, ![x,y] ∈ E ∧ ![x,z] ∈ E ∧ f y ≠ f z}

theorem sameProfile_definable (hp : B.real.Definable L p.codes)
    {f : M → Set (Fin m → M)} (hf : OverBase (L := L) p B (graph f)) :
    OverBase (L := L) p B (sameProfile f) := by
  let πx : Fin 1 ⊕ Fin m → Fin 2 ⊕ Fin m := Sum.elim (fun _ => .inl 0) Sum.inr
  let πy : Fin 1 ⊕ Fin m → Fin 2 ⊕ Fin m := Sum.elim (fun _ => .inl 1) Sum.inr
  have hx := hf.preimage_comp πx
  have hy := hf.preimage_comp πy
  have hi : OverBase (L := L) p B {z : Fin 2 ⊕ Fin m → M |
      z ∘ πx ∈ graph f ↔ z ∘ πy ∈ graph f} := by
    convert OverBase.compl
      (OverBase.inter
        (OverBase.compl (OverBase.inter hx hy hp) hp)
        (OverBase.compl (OverBase.inter (OverBase.compl hx hp) (OverBase.compl hy hp) hp) hp) hp) hp using 1
    ext z
    change (_ ↔ _) ↔ ¬ (¬ (_ ∧ _) ∧ ¬ (¬ _ ∧ ¬ _))
    tauto
  convert OverBase.forall_block hi hp using 1
  ext z
  change (f (z 0) = f (z 1)) ↔ ∀ t : Fin m → M, t ∈ f (z 0) ↔ t ∈ f (z 1)
  exact Set.ext_iff

theorem badPoints_definable (hp : B.real.Definable L p.codes)
    {E : Set (Fin 2 → M)} (hE : OverBase (L := L) p B E)
    {f : M → Set (Fin m → M)} (hf : OverBase (L := L) p B (graph f)) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ badPoints E f} := by
  have hx := hE.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 2)
  have hy := hE.preimage_comp (![Sum.inl 0,Sum.inr 1] : Fin 2 → Fin 1 ⊕ Fin 2)
  have hn := (OverBase.compl (sameProfile_definable hp hf) hp).preimage_comp
    (![Sum.inr 0,Sum.inr 1] : Fin 2 → Fin 1 ⊕ Fin 2)
  have hd := OverBase.exists_block (OverBase.inter hx (OverBase.inter hy hn hp) hp)
  convert hd using 1
  ext z
  have hxy (t : Fin 2 → M) :
      Sum.elim z t ∘ (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 2) = ![z 0,t 0] := by
    funext j; fin_cases j <;> rfl
  have hxz (t : Fin 2 → M) :
      Sum.elim z t ∘ (![Sum.inl 0,Sum.inr 1] : Fin 2 → Fin 1 ⊕ Fin 2) = ![z 0,t 1] := by
    funext j; fin_cases j <;> rfl
  change (∃ y t, ![z 0,y] ∈ E ∧ ![z 0,t] ∈ E ∧ f y ≠ f t) ↔
    ∃ t : Fin 2 → M, (Sum.elim z t ∘ ![Sum.inl 0,Sum.inr 0]) ∈ E ∧
      (Sum.elim z t ∘ ![Sum.inl 0,Sum.inr 1]) ∈ E ∧ f (t 0) ≠ f (t 1)
  simp only [hxy,hxz]
  exact ⟨fun ⟨y,t,hy,ht,hn⟩ => ⟨![y,t],hy,ht,hn⟩,
    fun ⟨a,hy,ht,hn⟩ => ⟨a 0,a 1,hy,ht,hn⟩⟩

/-- An atomic set meeting infinitely many classes avoids a definable union
of finitely many nonconstant classes. -/
theorem constant_on_classes (hp : B.real.Definable L p.codes)
    {C : Type*} (q : M → C) {A : Set M} (hA : IsAtomicOver (L := L) p B A)
    {f : M → Set (Fin m → M)} (hf : OverBase (L := L) p B (graph f))
    (hq : OverBase (L := L) p B {z : Fin 2 → M | q (z 0) = q (z 1)})
    (hbad : {c | ∃ x y, q x = c ∧ q y = c ∧ f x ≠ f y}.Finite)
    (hinf : (q '' A).Infinite) :
    ∀ x ∈ A, ∀ y ∈ A, q x = q y → f x = f y := by
  let E : Set (Fin 2 → M) := {z | q (z 0) = q (z 1)}
  have hd := badPoints_definable hp hq hf
  have hgood : ∃ x ∈ A, x ∉ badPoints E f := by
    by_contra hn
    apply hinf
    apply hbad.subset
    rintro c ⟨x,hx,rfl⟩
    have hb : x ∈ badPoints E f := by
      by_contra h
      exact hn ⟨x,hx,h⟩
    obtain ⟨y,z,hy,hz,hne⟩ := hb
    exact ⟨y,z,hy.symm,hz.symm,hne⟩
  have hdis : Disjoint A (badPoints E f) := by
    rcases hA.2 _ hd with hw | he
    · obtain ⟨x,hx,hg⟩ := hgood
      exact (hg (hw hx)).elim
    · exact he
  intro x hx y hy hxy
  by_contra hne
  exact Set.disjoint_left.mp hdis hx ⟨x,y,rfl,hxy,hne⟩

end IntegrationInACVF.Section3.ProfileAtomicity
