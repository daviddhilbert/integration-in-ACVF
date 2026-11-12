import IntegrationSection6.AlgebraicFibres
import Section4.RVProduct
import Section3.RVOperations
import Section3.GammaCodeDefinability

/-!
# Elementary RV blowups

Definition 6.1 on the predecessor's actual `RVObject`s, with a named
coordinate. `RV^{>1}` includes the single absorbing element: in the
Mathlib multiplicative valuation order its values are strictly below one.
The construction is available on arbitrary labels; `Admissible` supplies
the paper's hypotheses for an elementary blowup.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- The paper's `RV^{>1}`, including infinity (the absorbing RV zero). -/
def positiveRV (S : Set M) : DefSet (rawRVSpace (M := M) 1) S where
  carrier := {s | ¬ iLe (s 0).val iRVOne}
  definable := by
    have hr : (∅ : Set M).Definable LRV
        {z : Fin 1 → M | ¬ iLe (z (0 : Fin 1)) iRVOne} := by
      have hc : (∅ : Set M).DefinableFun LRV (fun _ : Fin 1 → M => iRVOne) :=
        SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.rvOne Fin.elim0 (fun i => i.elim0))
      have hm : (∅ : Set M).DefinableMap LRV (fun z : Fin 1 → M => ![z 0,iRVOne]) := by
        intro i; fin_cases i
        · exact Set.DefinableFun.proj LRV
        · exact hc
      exact (SpecialTransformations.Section3.GammaParameters.raw_le_definable (∅ : Set M)).preimage_map hm |>.compl
    have hd := (rawRVSpace (M := M) 1).definable_domain S
    change S.Definable LRV _
    convert hd.inter (hr.mono (Set.empty_subset S)) using 1
    ext z
    constructor
    · rintro ⟨hz, hs⟩
      refine ⟨hz, ?_⟩
      change ¬ iLe (z (0 : Fin 1)) iRVOne
      change ¬ iLe (((rawRVSpace (M := M) 1).decode ⟨z,hz⟩) 0).val iRVOne at hs
      have he := congrFun (rvValues_decode ⟨z,hz⟩) 0
      change (((rawRVSpace (M := M) 1).decode ⟨z,hz⟩) 0).val = z (0 : Fin 1) at he
      rwa [he] at hs
    · rintro ⟨hz, hs⟩
      refine ⟨hz, ?_⟩
      change ¬ iLe (((rawRVSpace (M := M) 1).decode ⟨z,hz⟩) 0).val iRVOne
      have he := congrFun (rvValues_decode ⟨z,hz⟩) 0
      change (((rawRVSpace (M := M) 1).decode ⟨z,hz⟩) 0).val = z (0 : Fin 1) at he
      rwa [he]

/-- Multiply the chosen label and retain all other labels. -/
def blowupValue (i : Fin k) (t : Fin k → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) : Fin k → CanonicalRV.RVSort M :=
  fun j => if j = i then s * t j else t j

@[simp] theorem blowupValue_same (i : Fin k) (t : Fin k → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) : blowupValue i t s i = s * t i := by
  simp [blowupValue]

@[simp] theorem blowupValue_other (i : Fin k) (t : Fin k → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) (j : Fin k) (hj : j ≠ i) : blowupValue i t s j = t j := by
  simp [blowupValue, hj]

/-- The label operation has a definable graph in the inherited language. -/
def blowupValueMap (S : Set M) (i : Fin k) :
    Map (DefSet.univ ((rawRVSpace (M := M) k).prod (rawRVSpace 1)) S)
      (DefSet.univ (rawRVSpace k) S) := by
  let P := (rawRVSpace (M := M) k).prod (rawRVSpace 1)
  let F (z : P.Index → M) : Fin k → M :=
    fun j => if j = i then iRVMul (z (.inr (0 : Fin 1))) (z (.inl j)) else z (.inl j)
  have hF : S.DefinableMap LRV F := by
    intro j
    by_cases hj : j = i
    · simp only [F, if_pos hj]
      exact (Set.DefinableFun.of_empty
        (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
          (show S.DefinableMap LRV (fun z : P.Index → M => ![z (.inr (0 : Fin 1)), z (.inl j)]) from
            fun l => by fin_cases l <;> exact Set.DefinableFun.proj LRV)
    · simp only [F, if_neg hj]
      exact Set.DefinableFun.proj LRV
  have hcode (c : P.domain) :
      rvValues (blowupValue i (P.decode c).1 ((P.decode c).2 0)) = F c.val := by
    have hl := rvValues_decode (M := M) (n := k) ⟨c.val ∘ Sum.inl, c.property.1⟩
    have hr := rvValues_decode (M := M) (n := 1) ⟨c.val ∘ Sum.inr, c.property.2⟩
    funext j
    by_cases hj : j = i
    · change (blowupValue i (P.decode c).1 ((P.decode c).2 0) j).val = _
      simp only [F, if_pos hj]
      rw [blowupValue, if_pos hj, RVOperations.mul_val]
      exact congrArg₂ iRVMul (congrFun hr 0) (congrFun hl j)
    · change (blowupValue i (P.decode c).1 ((P.decode c).2 0) j).val = _
      simp only [F, if_neg hj]
      rw [blowupValue_other i _ _ j hj]
      exact congrFun hl j
  refine Map.ofCodes _ (fun p => blowupValue i p.1 (p.2 0)) F hF
    (fun c => ⟨_, hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

/-- The packed real tuple presentation of `U × RV^{>1}`. -/
def elementary (U : RVObject (M := M) S k) (i : Fin k) : RVObject (M := M) S k where
  arity := U.arity + 1
  domain := rvProductDomain U.domain (positiveRV S)
  volume := (blowupValueMap S i).comp
    ((Map.prodMap U.volume (Map.id (positiveRV S))).toUniv.comp
      (rvUnpack U.domain (positiveRV S)))

/-- The actual projection from the elementary blowup to its original domain. -/
def elementaryProjection (U : RVObject (M := M) S k) (i : Fin k) :
    Map (elementary U i).domain U.domain :=
  (Map.prodFst U.domain (positiveRV S)).comp (rvUnpack U.domain (positiveRV S))

/-- The new RV coordinate, with its definable positivity condition. -/
def elementaryParameter (U : RVObject (M := M) S k) (i : Fin k) :
    Map (elementary U i).domain (positiveRV S) :=
  (Map.prodSnd U.domain (positiveRV S)).comp (rvUnpack U.domain (positiveRV S))

@[simp] theorem elementary_value (U : RVObject (M := M) S k) (i : Fin k)
    (a : (elementary U i).domain) :
    (elementary U i).value a = blowupValue i (U.value (elementaryProjection U i a))
      ((elementaryParameter U i a).val 0) := rfl

/-- Definition 6.1, including the chosen coordinate, its admissibility,
and an isomorphism to the canonical tuple presentation. -/
structure ElementaryBlowup (U V : RVObject (M := M) S k) where
  coordinate : Fin k
  admissible : Admissible U coordinate
  iso : V ≅ elementary U coordinate

theorem no_elementaryBlowup_degree_zero (U V : RVObject (M := M) S 0) :
    ¬ Nonempty (ElementaryBlowup U V) := by
  rintro ⟨h⟩
  exact h.coordinate.elim0

/-- Multiplication can remove a nonzero label only at the absorbing RV
parameter. In particular the projection has the required weight inequality. -/
theorem blowupValue_weight_le (i : Fin k) (t : Fin k → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) : rvWeight (blowupValue i t s) ≤ rvWeight t := by
  unfold rvWeight
  apply Finset.sum_le_sum
  intro j _
  have hz : (t j).val = iRVZero → (blowupValue i t s j).val = iRVZero := by
    intro hj
    have hzero : t j = 0 := Subtype.ext (hj.trans RVOperations.zero_val.symm)
    by_cases hji : j = i
    · simp only [blowupValue, if_pos hji, hzero, mul_zero, RVOperations.zero_val]
    · simpa only [blowupValue_other i t s j hji] using hj
  split_ifs with hn ho
  · exact le_rfl
  · exact False.elim (hn (hz (by simpa only [not_not] using ho)))
  · exact Nat.zero_le _
  · exact le_rfl

/-- Remark 6.2: the projection is an actual RV morphism. -/
def elementaryProjectionHom {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    RVHom (elementary U i) U where
  map := elementaryProjection U i
  volumetric a := blowupValue_weight_le i _ _
  finite_volume_images t := by
    apply (h.finite_label_fibres hκ hs hsmall t).subset
    rintro r ⟨a, ha, hr⟩
    refine ⟨⟨elementaryProjection U i a, hr⟩, ?_⟩
    intro j hj
    have hc : (elementary U i).value a j = U.value (elementaryProjection U i a) j := by
      rw [elementary_value, blowupValue_other i _ _ j hj]
    exact (congrFun hr j).symm.trans (hc.symm.trans (congrFun ha j))

/-- The raw order test agrees with the reversed Mathlib valuation order. -/
theorem positiveRV_iff_absolute_lt_one (s : Fin 1 → CanonicalRV.RVSort M) :
    s ∈ (positiveRV (M := M) S).carrier ↔ RVOperations.absoluteHom (s 0) < 1 := by
  have he := Values.valueEquiv_rv_le Values.presentationValuation
    Values.presentation_compatible (s 0) (1 : CanonicalRV.RVSort M)
  change iLe (s 0).val (1 : CanonicalRV.RVSort M).val ↔
    RVOperations.absoluteHom 1 ≤ RVOperations.absoluteHom (s 0) at he
  rw [RVOperations.one_val, map_one] at he
  exact (not_congr he).trans not_le

/-- Infinity belongs to the paper's positive RV factor. -/
theorem zero_mem_positiveRV :
    (fun _ : Fin 1 => (0 : CanonicalRV.RVSort M)) ∈ (positiveRV (M := M) S).carrier := by
  rw [positiveRV_iff_absolute_lt_one, map_zero]
  exact zero_lt_one

/-- Remark 6.2: elementary blowups preserve finite-to-one volume maps.
The new parameter is recovered by cancellation by the admissible nonzero
old label. Old labels form a finite set by genuine saturation. -/
theorem elementary_finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i)
    (hU : U.volume.FiniteFibres) : (elementary U i).volume.FiniteFibres := by
  intro t
  let R := {r | (∃ u : U.domain, U.value u = r) ∧ ∀ j, j ≠ i → r j = t.val j}
  have hR : R.Finite := h.finite_label_fibres hκ hs hsmall t.val
  have hF (r : Fin k → CanonicalRV.RVSort M) :
      {u : U.domain | U.value u = r}.Finite := by
    apply (hU ⟨r, Set.mem_univ _⟩).subset
    intro u hu
    exact Subtype.ext hu
  have hB := hR.biUnion (fun r _ => hF r)
  apply hB.of_injOn (f := elementaryProjection U i)
  · intro a ha
    refine Set.mem_iUnion.mpr ⟨U.value (elementaryProjection U i a),
      Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
    refine ⟨⟨elementaryProjection U i a, rfl⟩, ?_⟩
    intro j hj
    have he := congrFun (congrArg Subtype.val ha) j
    change (elementary U i).value a j = t.val j at he
    simpa only [elementary_value, blowupValue_other i _ _ j hj] using he
  · intro a ha b hb hab
    have hlabels := congrFun (congrArg Subtype.val (ha.trans hb.symm)) i
    change (elementary U i).value a i = (elementary U i).value b i at hlabels
    rw [elementary_value, elementary_value, blowupValue_same, blowupValue_same,
      ← hab] at hlabels
    have hn : U.value (elementaryProjection U i a) i ≠ 0 := by
      intro hz
      apply h.nonzero (elementaryProjection U i a)
      rw [hz, RVOperations.zero_val]
    have hp := mul_right_cancel₀ hn hlabels
    have he : rvUnpack U.domain (positiveRV S) a =
        rvUnpack U.domain (positiveRV S) b := by
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val hab
      · funext j
        fin_cases j
        exact hp
    have he' := congrArg (rvPack U.domain (positiveRV S)).toImage he
    simpa only [rvPack_unpack] using he'

end IntegrationInACVF.Section6
