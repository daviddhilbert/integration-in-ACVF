import IntegrationSection6.GammaFamilyValidity
import Section3.GammaClosureLaws
import Mathlib.Data.Set.Card

/-! The finite cardinality bounds used in blowup witness schemata are
first-order conditions on full original-Gamma tuple families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6

theorem finite_ncard_le_of_no_injective {X : Type*} (A : Set X) (N : ℕ)
    (h : ∀ f : Fin (N+1) → X, (∀ i, f i ∈ A) → ¬ Function.Injective f) :
    A.Finite ∧ A.ncard ≤ N := by
  apply Set.encard_le_coe_iff_finite_ncard_le.mp
  by_contra hn
  have hle : ((N+1 : ℕ) : ℕ∞) ≤ A.encard := by
    generalize he : A.encard = k at *
    cases k using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      simp only [Nat.cast_le] at *
      omega
  obtain ⟨f,hf,hi⟩ := (Set.le_encard_iff_exists_fin_injective A (N+1)).mp hle
  exact h f hf hi

theorem finite_ncard_le_iff_no_injective {X : Type*} (A : Set X) (N : ℕ) :
    (A.Finite ∧ A.ncard ≤ N) ↔
      ∀ f : Fin (N+1) → X, (∀ i, f i ∈ A) → ¬ Function.Injective f := by
  constructor
  · intro h f hf hi
    have hlo := (Set.le_encard_iff_exists_fin_injective A (N+1)).mpr ⟨f,hf,hi⟩
    have hhi := Set.encard_le_coe_iff_finite_ncard_le.mpr h
    have hbad : N+1 ≤ N := by exact_mod_cast hlo.trans hhi
    omega
  · exact finite_ncard_le_of_no_injective A N

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}
local notation "NStr" => (@CanonicalStructure.normalize M sM)

def familyBlockIndex (n m q : ℕ) (i : Fin q) : Fin (n+m) → Fin (n+q*m) :=
  Fin.addCases (Fin.castAdd (q*m)) (fun j => Fin.natAdd n (finProdFinEquiv (i,j)))

def familyBlockSort (sa : Fin n → SortTag) (sb : Fin m → SortTag) (q : ℕ) :
    Fin (n+q*m) → SortTag := Fin.append sa (fun j => sb (finProdFinEquiv.symm j).2)

theorem gamma_family_distinct_rows_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    (q : ℕ) (hq : 0 < q) {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase B (familyBlockSort sa sb q)
      {z | (∀ i : Fin q, z ∘ familyBlockIndex n m q i ∈ P) ∧
        Function.Injective (fun i : Fin q => fun j : Fin m => z (Fin.natAdd n (finProdFinEquiv (i,j))))} := by
  let S := B.real
  let st := familyBlockSort sa sb q
  let F (i : Fin q) : Set (Fin (n+q*m) → M) :=
    {z | z ∘ familyBlockIndex n m q i ∈ P ∧ z ∈ sortedUniverse st}
  have hF (i : Fin q) : DefinableOverBase B st (F i) := hP.preimage_real st _
  have hRows := DefinableOverBase.finite_iInter Finset.univ F (fun i _ => hF i)
  have hEq (i j : Fin q) : @Set.Definable M S LRV NStr (Fin (n+q*m))
      {z | (fun l : Fin m => z (Fin.natAdd n (finProdFinEquiv (i,l)))) =
        (fun l : Fin m => z (Fin.natAdd n (finProdFinEquiv (j,l))))} := by
    letI := NStr
    have hh (l : Fin m) := Set.DefinableFun.ofPred_eq
      (@Set.DefinableFun.proj M LRV NStr (Fin (n+q*m)) S (Fin.natAdd n (finProdFinEquiv (i,l))))
      (@Set.DefinableFun.proj M LRV NStr (Fin (n+q*m)) S (Fin.natAdd n (finProdFinEquiv (j,l))))
    convert Set.definable_iInter_of_finite hh using 1
    apply Set.ext
    intro z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact funext_iff
  have hInj : @Set.Definable M S LRV NStr (Fin (n+q*m))
      {z | Function.Injective (fun i : Fin q => fun j : Fin m => z (Fin.natAdd n (finProdFinEquiv (i,j))))} := by
    have hPair (i j : Fin q) : @Set.Definable M S LRV NStr (Fin (n+q*m))
        {z | (fun l : Fin m => z (Fin.natAdd n (finProdFinEquiv (i,l)))) =
          (fun l : Fin m => z (Fin.natAdd n (finProdFinEquiv (j,l)))) → i = j} := by
      letI := NStr
      by_cases hij : i = j
      · simpa [hij] using (@Set.definable_univ M S LRV NStr (Fin (n+q*m)))
      · simpa only [hij,imp_false,Set.compl_setOf] using (hEq i j).compl
    letI := NStr
    convert Set.definable_iInter_of_finite (fun i => Set.definable_iInter_of_finite (hPair i)) using 1
    apply Set.ext
    intro z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rfl
  have hSort := ((definableOver_iff_normalized_raw B.real st _).mp
    (sortedUniverse_definable B.real st)).1
  have hDistinct : DefinableOver B.real st
      {z | z ∈ sortedUniverse st ∧ Function.Injective (fun i : Fin q => fun j : Fin m =>
        z (Fin.natAdd n (finProdFinEquiv (i,j))))} := by
    apply (definableOver_iff_normalized_raw B.real st _).mpr
    letI := NStr
    exact ⟨hSort.inter hInj,fun _ h => h.1⟩
  have h := hRows.inter (real_definableOverBase B st _ hDistinct)
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hr,hi⟩
    have hs : z ∈ sortedUniverse st := by
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [familyBlockIndex,Function.comp_apply,Fin.addCases_left,familyBlockSort,st,Fin.append_left] using
          hP.proper _ (hr ⟨0,hq⟩) (Fin.castAdd m l)
      · have hp := hP.proper _ (hr (finProdFinEquiv.symm l).1)
          (Fin.natAdd n (finProdFinEquiv.symm l).2)
        simpa only [familyBlockIndex,Function.comp_apply,Fin.addCases_right,Prod.mk.eta,Equiv.apply_symm_apply,
          familyBlockSort,st,Fin.append_right] using hp
    exact ⟨⟨hs,fun i _ => ⟨hr i,hs⟩⟩,hs,hi⟩
  · rintro ⟨⟨_,hr⟩,_,hi⟩
    exact ⟨fun i => (hr i (Finset.mem_univ _)).1,hi⟩

theorem gamma_family_finite_bound_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    (N : ℕ) {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase B sa {a | (∀ i, sortEval (sa i) (a i)) ∧
      {x : Fin m → M | Fin.append a x ∈ P}.Finite ∧
      {x : Fin m → M | Fin.append a x ∈ P}.ncard ≤ N} := by
  let q := N+1
  let Q : Set (Fin (n+q*m) → M) :=
    {z | (∀ i : Fin q, z ∘ familyBlockIndex n m q i ∈ P) ∧
      Function.Injective (fun i : Fin q => fun j : Fin m => z (Fin.natAdd n (finProdFinEquiv (i,j))))}
  have hQ := gamma_family_distinct_rows_definable sa sb q (Nat.succ_pos N) hP
  have hp := hQ.image_real (Fin.castAdd (q*m))
  have hsort : familyBlockSort sa sb q ∘ Fin.castAdd (q*m) = sa := by
    funext i
    simp only [familyBlockSort,Function.comp_apply,Fin.append_left]
  rw [hsort] at hp
  have hbadiff (a : Fin n → M) : a ∈ (fun z => z ∘ Fin.castAdd (q*m)) '' Q ↔
      ∃ f : Fin q → (Fin m → M), (∀ i, Fin.append a (f i) ∈ P) ∧ Function.Injective f := by
    constructor
    · rintro ⟨z,⟨hz,hi⟩,ha⟩
      let f (i : Fin q) (j : Fin m) := z (Fin.natAdd n (finProdFinEquiv (i,j)))
      refine ⟨f,?_,hi⟩
      intro i
      have he : z ∘ familyBlockIndex n m q i = Fin.append a (f i) := by
        funext j
        refine Fin.addCases (fun l => ?_) (fun l => ?_) j
        · simpa only [familyBlockIndex,Function.comp_apply,Fin.addCases_left,Fin.append_left] using congrFun ha l
        · simp only [familyBlockIndex,Function.comp_apply,Fin.addCases_right,Fin.append_right,f]
      exact he ▸ hz i
    · rintro ⟨f,hf,hi⟩
      let z : Fin (n+q*m) → M := Fin.append a (fun j => f (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
      have he (i : Fin q) : z ∘ familyBlockIndex n m q i = Fin.append a (f i) := by
        funext j
        refine Fin.addCases (fun l => ?_) (fun l => ?_) j
        · simp only [z,familyBlockIndex,Function.comp_apply,Fin.addCases_left,Fin.append_left]
        · simp only [z,familyBlockIndex,Function.comp_apply,Fin.addCases_right,Fin.append_right,Equiv.symm_apply_apply]
      refine ⟨z,⟨fun i => (he i).symm ▸ hf i,?_⟩,?_⟩
      · simpa only [z,Fin.append_right,Equiv.symm_apply_apply] using hi
      · funext i
        exact Fin.append_left a _ i
  have hc := hp.compl
  convert hc using 1
  apply Set.ext
  intro a
  change ((∀ i, sortEval (sa i) (a i)) ∧ _) ↔
    (a ∈ sortedUniverse sa ∧ a ∉ (fun z => z ∘ Fin.castAdd (q*m)) '' Q)
  rw [hbadiff]
  simp only [not_exists,not_and]
  exact and_congr Iff.rfl (finite_ncard_le_iff_no_injective _ N)

end IntegrationInACVF.Section6
