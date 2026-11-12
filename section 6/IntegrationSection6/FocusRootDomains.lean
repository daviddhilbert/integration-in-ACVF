import Section7.LiftingDefinability

/-! Definable domains on which a field equation uniquely selects a focus.
The validity predicate quantifies over the whole RV fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] {n : ℕ}

def rootRelation (R : Set (Fin n → M)) (j : Fin n) : Set (Fin (n+n) → M) :=
  {z | z ∘ productRight n n ∈ R ∧ ∀ i, i ≠ j →
    z (productRight n n i) = z (productLeft n n i)}

theorem rootRelation_definable (S : Set M) (R : Set (Fin n → M))
    (hR : S.Definable LRV R) (j : Fin n) : S.Definable LRV (rootRelation R j) := by
  have h (i : {i : Fin n // i ≠ j}) : S.Definable LRV
      {z : Fin (n+n) → M | z (productRight n n i.val) = z (productLeft n n i.val)} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  convert (hR.preimage_comp (productRight n n)).inter
    (Set.definable_iInter_of_finite h) using 1
  ext z
  simp only [rootRelation, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_iInter, Subtype.forall]

def rootDomain (R : Set (Fin n → M)) (j : Fin n) : Set (Fin n → M) :=
  {t | ∀ a ∈ rawTupleFibre t, ∃! b, b ∈ rawTupleFibre t ∧
    b ∈ R ∧ ∀ i, i ≠ j → b i = a i}

theorem rootDomain_definable (S : Set M) (R : Set (Fin n → M))
    (hR : S.Definable LRV R) (j : Fin n) : S.Definable LRV (rootDomain R j) := by
  have h := rawOneWayLiftDomain_definable S (rootRelation R j)
    (rootRelation_definable S R hR j) (id : Fin n → Fin n) id finSumFinEquiv.symm
  convert h using 1
  ext t
  simp only [rootDomain, Set.mem_setOf_eq, Function.comp_id]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro ha
  apply existsUnique_congr
  intro b
  change (b ∈ rawTupleFibre t ∧ b ∈ R ∧ ∀ i, i ≠ j → b i = a i) ↔
    (b ∈ rawTupleFibre t ∧ Sum.elim a b ∘ finSumFinEquiv.symm ∈ rootRelation R j)
  change (b ∈ rawTupleFibre t ∧ b ∈ R ∧ ∀ i, i ≠ j → b i = a i) ↔
    (b ∈ rawTupleFibre t ∧ productTuple a b ∈ rootRelation R j)
  simp only [rootRelation,Set.mem_setOf_eq,Function.comp_def,productTuple_right,productTuple_left]

/-- On a fixed valid RV fibre, the selected point depends only on the
unmodified field coordinates. -/
theorem rootDomain_independent {R : Set (Fin n → M)} {j : Fin n}
    {t : Fin n → M} (ht : t ∈ rootDomain R j)
    {a a' b b' : Fin n → M} (ha : a ∈ rawTupleFibre t) (ha' : a' ∈ rawTupleFibre t)
    (haa' : ∀ i, i ≠ j → a i = a' i)
    (hb : b ∈ rawTupleFibre t ∧ b ∈ R ∧ ∀ i, i ≠ j → b i = a i)
    (hb' : b' ∈ rawTupleFibre t ∧ b' ∈ R ∧ ∀ i, i ≠ j → b' i = a' i) : b = b' := by
  apply (ht a ha).unique hb
  exact ⟨hb'.1, hb'.2.1, fun i hi => (hb'.2.2 i hi).trans (haa' i hi).symm⟩

def rawRVKey (a : Fin n → M) : Fin n → M := fun i => iRv (a i)

theorem rawRVKey_definable (S : Set M) : S.DefinableMap LRV (rawRVKey (M := M) (n := n)) := by
  intro i
  exact (Set.DefinableFun.of_empty
    (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show S.DefinableMap LRV (fun z : Fin n → M => ![z i]) from by
        intro k; fin_cases k; exact Set.DefinableFun.proj LRV)

theorem rawRVKey_eq {t a : Fin n → M} (ha : a ∈ rawTupleFibre t) : rawRVKey a = t :=
  funext (fun i => (ha i).2)

/-- Use the first equation valid on a whole RV fibre. The branch choice
is itself an RV predicate, so it never depends on the active VF variable. -/
def gluedRootSet {k : ℕ} (R : Fin k → Set (Fin n → M)) (j : Fin n) : Set (Fin n → M) :=
  {b | ∃ i, b ∈ R i ∧ rawRVKey b ∈ rootDomain (R i) j ∧
    ∀ l, l < i → rawRVKey b ∉ rootDomain (R l) j}

theorem gluedRootSet_definable (S : Set M) {k : ℕ}
    (R : Fin k → Set (Fin n → M)) (hR : ∀ i, S.Definable LRV (R i)) (j : Fin n) :
    S.Definable LRV (gluedRootSet R j) := by
  have hd (i : Fin k) : S.Definable LRV
      {b : Fin n → M | b ∈ R i ∧ rawRVKey b ∈ rootDomain (R i) j ∧
        ∀ l, l < i → rawRVKey b ∉ rootDomain (R l) j} := by
    have hcurrent := (rootDomain_definable S (R i) (hR i) j).preimage_map
      (rawRVKey_definable S)
    have hprior (l : {l : Fin k // l < i}) : S.Definable LRV
        {b : Fin n → M | rawRVKey b ∉ rootDomain (R l.val) j} :=
      ((rootDomain_definable S (R l.val) (hR l.val) j).preimage_map
        (rawRVKey_definable S)).compl
    convert (hR i).inter (hcurrent.inter (Set.definable_iInter_of_finite hprior)) using 1
    ext b
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iInter,
      Set.mem_compl_iff, Subtype.forall]
  convert Set.definable_iUnion_of_finite hd using 1
  ext b
  simp only [gluedRootSet, Set.mem_setOf_eq, Set.mem_iUnion]

theorem gluedRootSet_good {k : ℕ} (R : Fin k → Set (Fin n → M)) (j : Fin n)
    {t : Fin n → M} (ht : ∃ i, t ∈ rootDomain (R i) j) :
    t ∈ rootDomain (gluedRootSet R j) j := by
  let E : Finset (Fin k) := Finset.univ.filter (fun i => t ∈ rootDomain (R i) j)
  have hE : E.Nonempty := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := E.min' hE
  have hi : t ∈ rootDomain (R i) j := (Finset.mem_filter.mp (E.min'_mem hE)).2
  have hmin (l : Fin k) (hl : t ∈ rootDomain (R l) j) : i ≤ l :=
    E.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  have hfirst (l : Fin k) (hl : l < i) : t ∉ rootDomain (R l) j :=
    fun h => (not_le_of_gt hl) (hmin l h)
  intro a ha
  obtain ⟨b, hb, huniq⟩ := hi a ha
  refine ⟨b, ⟨hb.1, ⟨i, hb.2.1, ?_, ?_⟩, hb.2.2⟩, ?_⟩
  · simpa only [rawRVKey_eq hb.1] using hi
  · simpa only [rawRVKey_eq hb.1] using hfirst
  · intro c hc
    obtain ⟨l, hcl, hl, hlfirst⟩ := hc.2.1
    rw [rawRVKey_eq hc.1] at hl hlfirst
    have hli : l = i := by
      apply le_antisymm
      · by_contra hn
        exact hlfirst i (lt_of_not_ge hn) hi
      · exact hmin l hl
    subst l
    exact huniq c ⟨hc.1, hcl, hc.2.2⟩

/-- Compactness gives finitely many original-base equations; first-valid
RV gluing gives a single original-base root set on the entire family. -/
theorem exists_originalBase_rootSet [M ⊨ Axioms.ACVF]
    {κ : Cardinal} (hs : Saturated M κ) (S T : Set M) (hST : S ⊆ T)
    (hsmall : Cardinal.mk T < κ) (C : Set (Fin n → M)) (hC : T.Definable LRV C)
    (j : Fin n) (hloc : ∀ t ∈ C, ∃ R : Set (Fin n → M),
      S.Definable LRV R ∧ t ∈ rootDomain R j) :
    ∃ R : Set (Fin n → M), S.Definable LRV R ∧ C ⊆ rootDomain R j := by
  let D := {R : Set (Fin n → M) // S.Definable LRV R}
  let family := Set.range (fun R : D => rootDomain R.val j)
  have hfamily : ∀ d ∈ family, T.Definable LRV d := by
    rintro d ⟨R, rfl⟩
    exact (rootDomain_definable S R.val R.property j).mono hST
  have hcover : ∀ t ∈ C, ∃ d ∈ family, t ∈ d := by
    intro t ht
    obtain ⟨R, hR, htR⟩ := hloc t ht
    exact ⟨rootDomain R j, Set.mem_range_self (⟨R,hR⟩ : D), htR⟩
  obtain ⟨E,hE,hsub,hcov⟩ :=
    hs.definable_finite_subcover_tuple T hsmall C hC family hfamily hcover
  letI : Fintype E := hE.fintype
  let e := (Fintype.equivFin E).symm
  choose R hR using (fun i : Fin (Fintype.card E) => hsub (e i).property)
  refine ⟨gluedRootSet (fun i => (R i).val) j,
    gluedRootSet_definable S _ (fun i => (R i).property) j, ?_⟩
  intro t ht
  obtain ⟨d, hd, htd⟩ := hcov t ht
  obtain ⟨i, hi⟩ := e.surjective (⟨d, hd⟩ : E)
  apply gluedRootSet_good
  refine ⟨i, ?_⟩
  have hRi : rootDomain (R i).val j = (e i).val := hR i
  rw [hRi,hi]
  exact htd

end IntegrationInACVF.Section6
