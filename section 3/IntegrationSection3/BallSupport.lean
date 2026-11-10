module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.BooleanSubalgebra

@[expose] public section

/-!
# The finite-exception geometry behind Lemma 3.2

In a laminar collection (any two members are nested or disjoint), a set whose
membership is determined by finitely many balls can split only finitely many
members of a pairwise disjoint ball family. This proves the combinatorial part
of the paper's C-minimality argument, without assuming that conclusion as a
field of a model structure. Connecting this result to definability, algebraic
ball codes and the actual ACVF ball collection remains a separate obligation.
-/

open Set

namespace IntegrationInACVF.Section3

variable {X I : Type*}

/-- Membership in `S` takes both truth values on `C`. -/
def Splits (S C : Set X) : Prop :=
  ∃ x ∈ C, x ∈ S ∧ ∃ y ∈ C, y ∉ S

/-- The containment/disjointness property of open and closed valued-field balls. -/
def IsLaminar (balls : Set (Set X)) : Prop :=
  ∀ b ∈ balls, ∀ c ∈ balls, b ⊆ c ∨ c ⊆ b ∨ Disjoint b c

/-- A finite support for a Boolean combination, specified by pointwise membership.
The support balls need not be definable over the original parameter base. -/
def HasFiniteBallSupport (balls : Set (Set X)) (S : Set X) : Prop :=
  ∃ F : Finset (Set X), (∀ b ∈ F, b ∈ balls) ∧
    ∀ x y, (∀ b ∈ F, (x ∈ b ↔ y ∈ b)) → (x ∈ S ↔ y ∈ S)

theorem HasFiniteBallSupport.basic {balls : Set (Set X)} {b : Set X}
    (hb : b ∈ balls) : HasFiniteBallSupport balls b := by
  classical
  exact ⟨{b}, by simpa using hb, fun x y h => h b (Finset.mem_singleton_self b)⟩

theorem HasFiniteBallSupport.univ (balls : Set (Set X)) :
    HasFiniteBallSupport balls Set.univ := by
  classical
  exact ⟨∅, by simp, fun _ _ _ => Iff.rfl⟩

theorem HasFiniteBallSupport.compl {balls : Set (Set X)} {S : Set X}
    (hS : HasFiniteBallSupport balls S) : HasFiniteBallSupport balls Sᶜ := by
  obtain ⟨F, hF, hS⟩ := hS
  exact ⟨F, hF, fun x y h => not_congr (hS x y h)⟩

theorem HasFiniteBallSupport.union {balls : Set (Set X)} {S T : Set X}
    (hS : HasFiniteBallSupport balls S) (hT : HasFiniteBallSupport balls T) :
    HasFiniteBallSupport balls (S ∪ T) := by
  classical
  obtain ⟨F, hF, hS⟩ := hS
  obtain ⟨G, hG, hT⟩ := hT
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hF b hb
    · exact hG b hb
  · intro x y h
    exact or_congr (hS x y fun b hb => h b (Finset.mem_union_left G hb))
      (hT x y fun b hb => h b (Finset.mem_union_right F hb))

theorem HasFiniteBallSupport.inter {balls : Set (Set X)} {S T : Set X}
    (hS : HasFiniteBallSupport balls S) (hT : HasFiniteBallSupport balls T) :
    HasFiniteBallSupport balls (S ∩ T) := by
  simpa only [Set.compl_union, compl_compl] using (hS.compl.union hT.compl).compl

/-- Mathlib's Boolean closure provides finite support; this identifies the
support interface with the usual finite Boolean-combination construction. -/
theorem hasFiniteBallSupport_of_boolean_closure {balls : Set (Set X)} {S : Set X}
    (hS : S ∈ BooleanSubalgebra.closure balls) : HasFiniteBallSupport balls S := by
  apply BooleanSubalgebra.closure_bot_sup_induction
    (p := fun S _ => HasFiniteBallSupport balls S) ?_ ?_ ?_ ?_ hS
  · exact fun b hb => HasFiniteBallSupport.basic hb
  · simpa using (HasFiniteBallSupport.univ balls).compl
  · exact fun _ _ _ _ hS hT => hS.union hT
  · exact fun _ _ hS => hS.compl

/-- A ball splitting another ball must be contained in it. -/
theorem IsLaminar.subset_of_splits {balls : Set (Set X)} (h : IsLaminar balls)
    {b c : Set X} (hb : b ∈ balls) (hc : c ∈ balls) (hs : Splits b c) : b ⊆ c := by
  obtain ⟨x, hxc, hxb, y, hyc, hyb⟩ := hs
  rcases h b hb c hc with hbc | hcb | hdis
  · exact hbc
  · exact (hyb (hcb hyc)).elim
  · exact (Set.disjoint_left.mp hdis hxb hxc).elim

/-- One support ball can split at most one ball in a disjoint family. -/
theorem IsLaminar.subsingleton_splitters {balls : Set (Set X)} (h : IsLaminar balls)
    (C : I → Set X) (hC : ∀ i, C i ∈ balls)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    {b : Set X} (hb : b ∈ balls) : Set.Subsingleton {i | Splits b (C i)} := by
  intro i hi j hj
  by_contra hij
  obtain ⟨x, hxi, hxb, _⟩ := hi
  have hxj := h.subset_of_splits hb (hC j) hj hxb
  exact Set.disjoint_left.mp (hdis hij) hxi hxj

/-- If membership differs inside a family member, some support ball splits it. -/
theorem splits_support {F : Finset (Set X)} {S C : Set X}
    (hF : ∀ x y, (∀ b ∈ F, (x ∈ b ↔ y ∈ b)) → (x ∈ S ↔ y ∈ S))
    (hs : Splits S C) : ∃ b ∈ F, Splits b C := by
  classical
  obtain ⟨x, hxc, hxS, y, hyc, hyS⟩ := hs
  by_contra hn
  apply hyS
  apply (hF x y ?_).mp hxS
  intro b hb
  constructor
  · intro hxb
    by_contra hyb
    exact hn ⟨b, hb, x, hxc, hxb, y, hyc, hyb⟩
  · intro hyb
    by_contra hxb
    exact hn ⟨b, hb, y, hyc, hyb, x, hxc, hxb⟩

/-- Core of Lemma 3.2: a finite Boolean combination of balls has only finitely
many proper nonempty traces on a disjoint family of balls. -/
theorem finite_splitters {balls : Set (Set X)} (h : IsLaminar balls)
    (C : I → Set X) (hC : ∀ i, C i ∈ balls)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    {S : Set X} (hS : HasFiniteBallSupport balls S) :
    {i | Splits S (C i)}.Finite := by
  classical
  obtain ⟨F, hF, hS⟩ := hS
  have hfinite : (⋃ b ∈ (F : Set (Set X)), {i | Splits b (C i)}).Finite :=
    F.finite_toSet.biUnion fun b hb => (h.subsingleton_splitters C hC hdis (hF b hb)).finite
  apply hfinite.subset
  intro i hi
  obtain ⟨b, hb, hbi⟩ := splits_support hS hi
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hbi⟩⟩

/-- The finite-exception conclusion stated using the standard Boolean closure. -/
theorem finite_splitters_of_boolean_closure {balls : Set (Set X)} (h : IsLaminar balls)
    (C : I → Set X) (hC : ∀ i, C i ∈ balls)
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    {S : Set X} (hS : S ∈ BooleanSubalgebra.closure balls) :
    {i | Splits S (C i)}.Finite :=
  finite_splitters h C hC hdis (hasFiniteBallSupport_of_boolean_closure hS)

end IntegrationInACVF.Section3
